# Copyright 2016-2026 The OpenSSL Project Authors. All Rights Reserved.
#
# Licensed under the Apache License 2.0 (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

use strict;

use TLSProxy::Proxy;

package TLSProxy::Record;

my $server_encrypting = 0;
my $client_encrypting = 0;
my $etm = 0;

# Per-direction view of the peer's epoch, and the right edge of its replay
# window per (direction, epoch).  A unified header carries only epoch mod 4
# and 8 or 16 bits of the sequence number, so both have to be reconstructed
# from what has already been seen from that direction, as the receiver does.
my %epoch_seen;
my %seq_window;

# Shape of the unified headers this connection actually uses, per direction:
# the S and L bits of the last record parsed from it.  Records the proxy builds
# itself should match the peer rather than a hardcoded shape.
my %uni_shape;

# Records discarded instead of parsed, so a recipe can assert on the drop.
my $cid_dropped = 0;
my $short_dropped = 0;

use constant DTLS_RECORD_HEADER_LENGTH => 13;
use constant TLS_RECORD_HEADER_LENGTH => 5;

# A DTLSCiphertext body has to hold at least an AEAD tag and the trailing inner
# content type byte. DTLS13_CIPHERTEXT_MINSIZE is include/openssl/dtls1.h; the
# receiver enforces it at ssl/record/methods/dtls_meth.c.
use constant DTLS13_CIPHERTEXT_MINSIZE => 16;
use constant DTLS13_UNI_BODY_MIN => DTLS13_CIPHERTEXT_MINSIZE + 1;

#Record types
use constant {
    RT_APPLICATION_DATA   => 23,
    RT_HANDSHAKE          => 22,
    RT_ALERT              => 21,
    RT_CCS                => 20,
    RT_ACK                => 26,
    RT_UNKNOWN            => 100,
    RT_DTLS_UNIHDR_EPOCH4 => 0x2c,
    RT_DTLS_UNIHDR_EPOCH1 => 0x2d,
    RT_DTLS_UNIHDR_EPOCH2 => 0x2e,
    RT_DTLS_UNIHDR_EPOCH3 => 0x2f,
};

my %record_type = (
    RT_APPLICATION_DATA, "APPLICATION DATA",
    RT_HANDSHAKE, "HANDSHAKE",
    RT_ALERT, "ALERT",
    RT_CCS, "CCS",
    RT_ACK, "ACK",
    RT_UNKNOWN, "UNKNOWN",
);

# The sixteen unified first bytes, generated from the bit definitions so a
# mistyped key cannot silently shadow another one: 0x21 was written twice and
# 0x2a was missing, so S=0,L=0,EE=01 printed "EPOCH 2" and S=1,L=0,EE=10
# printed nothing. Epoch 0 is never carried by a unified header, so the EE bits
# name epochs 1..4 and the label keeps the RFC 9147 section 4.2.3 spelling.
my @uni_epoch_of = (4, 1, 2, 3);
for my $s (0, 1) {
    for my $l (0, 1) {
        for my $ee (0 .. 3) {
            $record_type{0x20 | ($s << 3) | ($l << 2) | $ee} =
                "DTLS UNIFIED HEADER (EPOCH $uni_epoch_of[$ee])";
        }
    }
}

use constant {
    VERS_DTLS_1_3 => 0xfefc,
    VERS_DTLS_1_2 => 0xfefd,
    VERS_DTLS_1 => 0xfeff,
    VERS_TLS_1_4 => 0x0305,
    VERS_TLS_1_3 => 0x0304,
    VERS_TLS_1_2 => 0x0303,
    VERS_TLS_1_1 => 0x0302,
    VERS_TLS_1_0 => 0x0301,
    VERS_SSL_3_0 => 0x0300,
    VERS_SSL_LT_3_0 => 0x02ff
};

our %tls_version = (
    VERS_DTLS_1_3, "DTLS1.3",
    VERS_DTLS_1_2, "DTLS1.2",
    VERS_DTLS_1, "DTLS1",
    VERS_TLS_1_3, "TLS1.3",
    VERS_TLS_1_2, "TLS1.2",
    VERS_TLS_1_1, "TLS1.1",
    VERS_TLS_1_0, "TLS1.0",
    VERS_SSL_3_0, "SSL3",
    VERS_SSL_LT_3_0, "SSL<3"
);

# Port of dtls13_reconstruct_seq_num() (ssl/record/methods/dtls_meth.c).
# Selects the candidate closest to the right edge of the replay window plus
# one, ignoring candidates outside the sequence-number range and breaking ties
# forward.  An empty window is represented by max_seq_num == 0.  Sequence
# numbers near 2**64 are unreachable in a proxy session, so the UINT64_MAX
# wrap handling of the C original is left out.
sub dtls13_reconstruct_seq_num
{
    my ($max_seq_num, $truncated, $seqlen) = @_;

    my $mask = (1 << (8 * $seqlen)) - 1;
    my $period = $mask + 1;
    my $expected = $max_seq_num + 1;

    # The candidate in the same period-sized block as $expected
    my $candidate = ($expected & ~$mask) | $truncated;
    my $best = $candidate;
    my $best_dist = abs($candidate - $expected);

    # The candidate one period behind, if it does not underflow
    if ($candidate >= $period) {
        my $alt = $candidate - $period;
        my $dist = abs($alt - $expected);
        # Strictly closer only: a tie goes to the forward candidate
        if ($dist < $best_dist) {
            $best = $alt;
            $best_dist = $dist;
        }
    }

    # The candidate one period ahead
    my $alt = $candidate + $period;
    my $dist = abs($alt - $expected);
    # Ties go forward
    if ($dist <= $best_dist) {
        $best = $alt;
    }

    return $best;
}

# The wire carries epoch mod 4 -- dtls_prepare_record_header() writes
# rl->epoch & DTLS13_UNI_HDR_EPOCH_BITS_MASK -- so it is resolved against the
# epochs already seen from this direction: the candidate congruent to $ee
# modulo 4 that is closest to the next expected epoch, without going backwards.
# Epoch 0 is never sent with a unified header, so 1 is the lowest candidate.
#
# Monotone by design, which means a retransmission of a record from an epoch
# more than three epochs behind the current one resolves too far forward.  The
# proxy keeps no epoch list, so it cannot do better, and no recipe exercises
# that today.
sub resolve_epoch
{
    my ($serverissender, $ee) = @_;

    my $current = $epoch_seen{$serverissender} // 0;
    my $lowest = $current < 1 ? 1 : $current;
    my $expected = $current + 1;

    # First candidate at or after $expected with candidate % 4 == $ee
    my $best = $expected + ((($ee - $expected) % 4) + 4) % 4;
    my $best_dist = $best - $expected;

    my $alt = $best - 4;
    if ($alt >= $lowest && $expected - $alt < $best_dist) {
        $best = $alt;
    }

    $epoch_seen{$serverissender} = $best if $best > $current;
    return $best;
}

# Serialise a unified header and hand it back, the single place that knows the
# shape rules.  $first is the numeric first byte, carrying the fix bits and the
# C, S, L and EE bits; the sequence number is masked with the leading bytes of
# the body exactly as dtls_prepare_record_header() does, so passing the
# reconstructed value puts the original truncated bits back on the wire (see
# the note in get_records() about the ossltest no-op cipher).  $len is only
# emitted when L is set.
sub encode_unified_header
{
    my ($first, $seq, $len, $body) = @_;

    $body = '' unless defined $body;
    my ($sbit, $lbit) = ($first & 0x08 ? 1 : 0, $first & 0x04 ? 1 : 0);
    my ($maskhi) = unpack('n', substr($body . "\0\0", 0, 2));

    my $hdr = chr($first);
    if ($sbit) {
        $hdr .= pack('n', ($seq & 0xffff) ^ $maskhi);
    } else {
        $hdr .= pack('C', ($seq & 0xff) ^ ($maskhi >> 8));
    }
    $hdr .= pack('n', $len) if $lbit;

    return $hdr;
}

#Class method to extract records from a packet of data
sub get_records
{
    my $class = shift;
    my $serverissender = shift;
    my $flight = shift;
    my $packet = shift;
    my $isdtls = shift;
    my $partial = "";
    my @record_list = ();
    my @message_list = ();

    my $recnum = 1;
    while (length ($packet) > 0) {
        print " Record $recnum ", $serverissender ? "(server -> client)\n"
                                                  : "(client -> server)\n";
        my $record_hdr_len;
        my $content_type;
        my $version;
        my $len;
        my $epoch;
        my $seq;
        my $isunifiedhdr;
        my $sbit = 0;
        my $lbit = 0;

        if ($isdtls == 1) {

            $content_type = unpack('B[8]', $packet);
            $isunifiedhdr = substr($content_type, 0, 3) == "001";

            if ($isunifiedhdr == 1) {
                my $cbit = substr($content_type, 3, 1);
                $sbit = substr($content_type, 4, 1);
                $lbit = substr($content_type, 5, 1);
                my $eebits = substr($content_type, 6, 2);

                if ($cbit == "1") {
                    # The record layer silently discards a record whose
                    # Connection ID bit is set (dtls_get_more_records() in
                    # ssl/record/methods/dtls_meth.c).  Dying here took the
                    # whole recipe down with it.
                    $cid_dropped++;
                    print "  Connection ID in a unified header is not"
                          ." supported, dropping the datagram\n";
                    $packet = "";
                    last;
                }
                $uni_shape{$serverissender} = substr($packet, 0, 1);

                $record_hdr_len = 2 + ($sbit == "1" ? 1 : 0)
                                     + ($lbit == "1" ? 2 : 0);
                # A datagram that does not even hold the header is truncated.
                # Unpacking it anyway yields an undef length, and the record
                # ends up claiming a negative one.
                if (length($packet) < $record_hdr_len) {
                    print "Partial data : ".length($packet)." bytes\n";
                    $partial = $packet;
                    last;
                }

                # This is a unified header
                if ($lbit == "1") {
                    if ($sbit == "1") {
                        ($content_type, $seq, $len) = unpack('Cnn', $packet);
                    } else {
                        ($content_type, $seq, $len) = unpack('CCn', $packet);
                    }
                } else {
                    if ($sbit == "1") {
                        ($content_type, $seq) = unpack('Cn', $packet);
                    } else {
                        ($content_type, $seq) = unpack('CC', $packet);
                    }
                    $len = length($packet) - $record_hdr_len;
                }

                # The receiver requires at least DTLS13_CIPHERTEXT_MINSIZE
                # bytes of ciphertext plus the trailing inner content type.  A
                # shorter body would hand decrypt() a negative substr length,
                # which Perl reads as "strip from the end" and returns as
                # plaintext.
                if ($len < DTLS13_UNI_BODY_MIN) {
                    print "  Unified record body of $len bytes is too short,"
                          ." dropping\n";
                    $short_dropped++;
                    $packet = substr($packet, $record_hdr_len + $len);
                    $recnum++;
                    next;
                }

                # Encrypted DTLS 1.3 records have encrypted sequence numbers.
                # ossltest engine overrides ecb encryption to be a no-op.
                # This effectively means that the sequence number encryption mask
                # is just the 16 first bytes of the record body.
                my $recordbody = substr($packet, $record_hdr_len, $len);
                (my $maskhi, my $maskmi, my $masklo) = unpack('nnn', $recordbody);
                $version = VERS_DTLS_1_2; # DTLSv1.3 headers has DTLSv1.2 in its legacy_version field

                die("Epoch bits is not 0's or 1's: should not happen")
                    unless $eebits =~ /^[01]{2}$/;
                $epoch = resolve_epoch($serverissender, oct("0b$eebits"));

                if ($sbit == "1") {
                    $seq ^= $maskhi;
                } else {
                    $seq ^= $maskhi >> 8;
                }

                # The wire carries only 8 or 16 bits of the sequence number, so
                # the full value has to come from this (direction, epoch) replay
                # window, as dtls_get_records() does. The low bits still equal
                # the truncated wire value, which is what reconstruct_record()
                # masks back and re-serialises.
                my $winkey = $serverissender . ':' . $epoch;
                my $max_seq_num = $seq_window{$winkey} // 0;
                $seq = dtls13_reconstruct_seq_num($max_seq_num, $seq,
                                                  $sbit == "1" ? 2 : 1);
                $seq_window{$winkey} = $seq if $seq > $max_seq_num;
            } else {
                my $seqhi;
                my $seqmi;
                my $seqlo;
                #Get the record header (unpack can't fail if $packet is too short)
                ($content_type, $version, $epoch,
                    $seqhi, $seqmi, $seqlo, $len) = unpack('Cnnnnnn', $packet);
                $seq = ($seqhi << 32) | ($seqmi << 16) | $seqlo;
                $record_hdr_len = DTLS_RECORD_HEADER_LENGTH;
            }
        } else {
            #Get the record header (unpack can't fail if $packet is too short)
            ($content_type, $version, $len) = unpack('Cnn', $packet);
            $record_hdr_len = TLS_RECORD_HEADER_LENGTH;
        }

        if (length($packet) < $record_hdr_len + ($len // 0)) {
            print "Partial data : ".length($packet)." bytes\n";
            $partial = $packet;
            last;
        }

        my $data = substr($packet, $record_hdr_len, $len);

        print "  Content type: ".$record_type{$content_type}."\n";
        print "  Version: $tls_version{$version}\n";
        if($isdtls == 1) {
            print "  Epoch: $epoch\n";
            print "  Sequence: $seq\n";
        }
        print "  Length: $len\n";

        my $record;
        if ($isdtls) {
            $record = TLSProxy::Record->new_dtls(
                $serverissender,
                $flight,
                $content_type,
                $version,
                $epoch,
                $seq,
                $len,
                $len,       # len_real
                $len,       # decrypt_len
                $data,      # data
                $data,      # decrypt_data
                $isunifiedhdr ? 1 : 0,
                $isunifiedhdr ? 0 + $sbit : 0,
                $isunifiedhdr ? 0 + $lbit : 0
            );
        } else {
            $record = TLSProxy::Record->new(
                $serverissender,
                $flight,
                $content_type,
                $version,
                $len,
                $len,  # len_real
                $len,  # decrypt_len
                $data, # data
                $data  # decrypt_data
            );
        }

        if ($content_type != RT_CCS
                && (!TLSProxy::Proxy->is_tls13()
                    || !$isdtls && $content_type != RT_ALERT
                    || $isunifiedhdr)) {
            # A unified header is DTLSCiphertext by definition, so it is
            # de-protected whenever it is parsed. The connection level
            # encryption flags are set while the ServerHello is being parsed,
            # so records that arrive early (0-RTT, or a keyed record buffered
            # behind an epoch 0 flight) must not depend on them.
            if (($serverissender && $server_encrypting)
                     || (!$serverissender && $client_encrypting) || $isunifiedhdr) {
                if (!$isunifiedhdr && !TLSProxy::Proxy->is_tls13() && $etm) {
                    $record->decryptETM();
                } else {
                    $record->decrypt();
                }
                $record->encrypted(1);

                if (TLSProxy::Proxy->is_tls13()) {
                    print "  Inner content type: "
                          .$record_type{$record->content_type()}."\n";
                    print " Data: ".unpack("n",$record->decrypt_data)."\n";
                }
            }
        }

        push @record_list, $record;

        #Now figure out what messages are contained within this record
        my @messages = TLSProxy::Message->get_messages($record);
        push @message_list, @messages;

        $packet = substr($packet, $record_hdr_len + $len);
        $recnum++;
    }

    return (\@record_list, \@message_list, $partial);
}

sub clear
{
    $server_encrypting = 0;
    $client_encrypting = 0;
    %epoch_seen = ();
    %seq_window = ();
    %uni_shape = ();
    $cid_dropped = 0;
    $short_dropped = 0;
}

# Read-only counters for the two ways a unified record is discarded rather than
# parsed: the Connection ID bit is set, or the body is too short to de-protect.
sub cid_dropped
{
    return $cid_dropped;
}
sub short_dropped
{
    return $short_dropped;
}

# The (S, L) bit pair of the unified headers seen from $serverissender, defaulting
# to the minimal header when nothing has been parsed from that direction yet.
sub uni_shape
{
    my ($class, $serverissender) = @_;
    my $shape = $uni_shape{$serverissender // 0};

    return defined $shape ? (ord($shape) & 0x08 ? 1 : 0,
                             ord($shape) & 0x04 ? 1 : 0)
                          : (0, 0);
}

#Class level accessors
sub server_encrypting
{
    my $class = shift;
    if (@_) {
      $server_encrypting = shift;
    }
    return $server_encrypting;
}
sub client_encrypting
{
    my $class = shift;
    if (@_) {
      $client_encrypting= shift;
    }
    return $client_encrypting;
}
#Enable/Disable Encrypt-then-MAC
sub etm
{
    my $class = shift;
    if (@_) {
      $etm = shift;
    }
    return $etm;
}

# The last three arguments describe the wire format and are optional for
# records a test builds itself: a DTLS 1.3 record in a keyed epoch is
# DTLSCiphertext, which is the rule dtls_prepare_record_header() applies.
# get_records() always passes them explicitly, because for a parsed record
# only the header itself decides the format.
sub new_dtls
{
    my $class = shift;
    my ($serverissender,
        $flight,
        $content_type,
        $version,
        $epoch,
        $seq,
        $len,
        $len_real,
        $decrypt_len,
        $data,
        $decrypt_data,
        $unified,
        $unified_sbit,
        $unified_lbit) = @_;

    # Only records a test builds itself reach here without a header to read,
    # so the connection's negotiated version is the only DTLS 1.3 signal
    # available: the version field of a unified record reads as DTLS 1.2.
    # get_records() always passes $unified explicitly, so a parsed record never
    # depends on this.
    $unified = defined $unified
               ? ($unified ? 1 : 0)
               : ($epoch > 0 && TLSProxy::Proxy->is_tls13() ? 1 : 0);
    if (!$unified) {
        $unified_sbit = 0;
        $unified_lbit = 0;
    } else {
        # Default to the minimal header: no sequence number field beyond one
        # byte and no length field.
        $unified_sbit = defined $unified_sbit ? ($unified_sbit ? 1 : 0) : 0;
        $unified_lbit = defined $unified_lbit ? ($unified_lbit ? 1 : 0) : 0;
    }

    my $self = $class->init($serverissender,
        1,
        $flight,
        $content_type,
        $version,
        $epoch,
        $seq,
        $len,
        $len_real,
        $decrypt_len,
        $data,
        $decrypt_data,
        $unified,
        $unified_sbit,
        $unified_lbit);

    # A unified header carries no content type: the first byte is the header
    # itself, and the content type travels inside the payload. Derive it the
    # way dtls_prepare_record_header() does. For a record that came off the
    # wire this reproduces the byte that was read, because that byte is the
    # same function of the same three fields.
    $self->outer_content_type(0x20 | ($unified_sbit << 3)
                                    | ($unified_lbit << 2)
                                    | ($epoch & 0x03)) if $unified;

    return $self;
}

sub new
{
    my $class = shift;
    my ($serverissender,
        $flight,
        $content_type,
        $version,
        $len,
        $len_real,
        $decrypt_len,
        $data,
        $decrypt_data) = @_;
    return $class->init(
        $serverissender,
        0,
        $flight,
        $content_type,
        $version,
        0, #epoch
        0, #seq
        $len,
        $len_real,
        $decrypt_len,
        $data,
        $decrypt_data);
}

sub init
{
    my $class = shift;
    my ($serverissender,
        $isdtls,
        $flight,
        $content_type,
        $version,
        $epoch,
        $seq,
        $len,
        $len_real,
        $decrypt_len,
        $data,
        $decrypt_data,
        $unified,
        $unified_sbit,
        $unified_lbit) = @_;

    my $self = {
        serverissender => $serverissender,
        isdtls => $isdtls,
        flight => $flight,
        content_type => $content_type,
        version => $version,
        epoch => $epoch,
        seq => $seq,
        len => $len,
        len_real => $len_real,
        decrypt_len => $decrypt_len,
        data => $data,
        decrypt_data => $decrypt_data,
        orig_decrypt_data => $decrypt_data,
        sent => 0,
        encrypted => 0,
        outer_content_type => $content_type,
        aead_unwrapped => 0,
        unified => $unified // 0,
        unified_sbit => $unified_sbit // 0,
        unified_lbit => $unified_lbit // 0,
    };

    return bless $self, $class;
}

#Decrypt using encrypt-then-MAC
sub decryptETM
{
    my ($self) = shift;

    my $data = $self->data;

    if((!$self->{isdtls} && $self->version >= VERS_TLS_1_1)
       || ($self->{isdtls} && $self->version <= VERS_DTLS_1)) {
        #TLS1.1+ has an explicit IV. Throw it away
        $data = substr($data, 16);
    }

    #Throw away the MAC (assumes MAC is 20 bytes for now. FIXME)
    $data = substr($data, 0, length($data) - 20);

    #Find out what the padding byte is
    my $padval = unpack("C", substr($data, length($data) - 1));

    #Throw away the padding
    $data = substr($data, 0, length($data) - ($padval + 1));

    $self->decrypt_data($data);
    $self->decrypt_len(length($data));

    return $data;
}

#Standard decrypt
sub decrypt()
{
    my ($self) = shift;
    my $mactaglen = 20;
    my $data = $self->data;
    # A unified header is DTLSCiphertext, so it is always AEAD sealed. It must
    # not fall through to the CBC branch below just because the connection has
    # not parsed its ServerHello yet.
    my $aead = TLSProxy::Proxy->is_tls13() || $self->{unified};

    #Throw away any IVs
    if ($aead) {
        #A TLS1.3 client, when processing the server's initial flight, could
        #respond with either an encrypted or an unencrypted alert.
        #A unified record cannot be one: its content type is still the raw
        #0x2x header byte at this point, so exclude it by hand rather than
        #relying on that.
        if (!$self->{unified} && $self->content_type() == RT_ALERT) {
            #TODO(TLS1.3): Eventually it is sufficient just to check the record
            #content type. If an alert is encrypted it will have a record
            #content type of application data. However we haven't done the
            #record layer changes yet, so it's a bit more complicated. For now
            #we will additionally check if the data length is 2 (1 byte for
            #alert level, 1 byte for alert description). If it is, then this is
            #an unencrypted alert, so don't try to decrypt
            return $data if (length($data) == 2);
        }
        $mactaglen = 16;
    } elsif ((!$self->{isdtls} && $self->version() >= VERS_TLS_1_1)
             || ($self->{isdtls} && $self->version() <= VERS_DTLS_1)) {
        #16 bytes for a standard IV
        $data = substr($data, 16);

        #Find out what the padding byte is
        my $padval = unpack("C", substr($data, length($data) - 1));

        #Throw away the padding
        $data = substr($data, 0, length($data) - ($padval + 1));
    }

    #Throw away the MAC or TAG
    $data = substr($data, 0, length($data) - $mactaglen);

    if ($aead) {
        #Get the content type
        my $content_type = unpack("C", substr($data, length($data) - 1));
        $self->content_type($content_type);
        $data = substr($data, 0, length($data) - 1);
        # The content type that travels on the wire is the one that was
        # replaced above, so re-serialisation has to reach for it explicitly.
        $self->{aead_unwrapped} = 1;
    }

    $self->decrypt_data($data);
    $self->decrypt_len(length($data));

    return $data;
}

#Reconstruct the on-the-wire record representation
sub reconstruct_record
{
    my $self = shift;
    my $server = shift;
    my $data;

    #We only replay the records in the same direction
    if ($self->{sent} || ($self->flight & 1) != $server) {
        return "";
    }
    $self->{sent} = 1;

    # Which header to emit is a property of the record, never of the
    # connection: is_tls13() and encrypted() both flip mid-connection, and
    # clearClient() resets them while records from the previous connection are
    # still queued. The content type on the wire is whatever the record layer
    # had before decrypt() replaced it with the inner one.
    my $content_type = ($self->{unified} || $self->{aead_unwrapped})
                       ? $self->outer_content_type : $self->content_type;
    if($self->{isdtls}) {
        if ($self->{unified}) {
            $data = encode_unified_header($content_type, $self->seq,
                                          $self->len, $self->data);
        } else {
            my $seqhi = ($self->seq >> 32) & 0xffff;
            my $seqmi = ($self->seq >> 16) & 0xffff;
            my $seqlo = ($self->seq >> 0) & 0xffff;

            $data = pack('Cnnnnnn', $content_type, $self->version,
                $self->epoch, $seqhi, $seqmi, $seqlo, $self->len);
        }
    } else {
        $data = pack('Cnn', $content_type, $self->version, $self->len);
    }

    $data .= $self->data;

    return $data;
}

sub get_actual_acked_record_numbers
{
    my $self = shift;
    my $record_numbers = shift;

    if ($self->content_type == TLSProxy::Record::RT_ACK) {
        my $recnum_count = unpack('n', $self->decrypt_data) / 16;
        my $ptr = 2;

        for (my $idx = 0; $idx < $recnum_count; $idx++) {
            my $epoch_lo;
            my $epoch_hi;
            my $msgseq_lo;
            my $msgseq_hi;

            ($epoch_hi, $epoch_lo, $msgseq_hi, $msgseq_lo)
                = unpack('NNNN', substr($self->decrypt_data, $ptr));
            $ptr = $ptr + 16;

            my $epoch = ($epoch_hi << 32) | $epoch_lo;
            my $msgseq = ($msgseq_hi << 32) | $msgseq_lo;
            my $recnum = TLSProxy::RecordNumber->new($epoch, $msgseq);

            push(@$record_numbers, $recnum);
        }
    }
}

#Read only accessors
sub serverissender
{
    my $self = shift;
    return $self->{serverissender};
}
sub isdtls
{
    my $self = shift;
    return $self->{isdtls};
}
# How the record arrived on the wire. Read only: reconstructing it in a
# different shape would make the proxy's output unparseable for the peer.
sub unified
{
    my $self = shift;
    return $self->{unified};
}
sub unified_sbit
{
    my $self = shift;
    return $self->{unified_sbit};
}
sub unified_lbit
{
    my $self = shift;
    return $self->{unified_lbit};
}
sub flight
{
    my $self = shift;
    return $self->{flight};
}
sub len_real
{
    my $self = shift;
    return $self->{len_real};
}
sub orig_decrypt_data
{
    my $self = shift;
    return $self->{orig_decrypt_data};
}

#Read/write accessors
sub decrypt_len
{
    my $self = shift;
    if (@_) {
      $self->{decrypt_len} = shift;
    }
    return $self->{decrypt_len};
}
sub data
{
    my $self = shift;
    if (@_) {
      $self->{data} = shift;
    }
    return $self->{data};
}
sub decrypt_data
{
    my $self = shift;
    if (@_) {
      $self->{decrypt_data} = shift;
    }
    return $self->{decrypt_data};
}
sub len
{
    my $self = shift;
    if (@_) {
      $self->{len} = shift;
    }
    return $self->{len};
}
sub version
{
    my $self = shift;
    if (@_) {
      $self->{version} = shift;
    }
    return $self->{version};
}
sub content_type
{
    my $self = shift;
    if (@_) {
      $self->{content_type} = shift;
    }
    return $self->{content_type};
}
sub epoch
{
    my $self = shift;
    if (@_) {
        $self->{epoch} = shift;
    }
    return $self->{epoch};
}
sub seq
{
    my $self = shift;
    if (@_) {
        $self->{seq} = shift;
    }
    return $self->{seq};
}
sub encrypted
{
    my $self = shift;
    if (@_) {
      $self->{encrypted} = shift;
    }
    return $self->{encrypted};
}
sub outer_content_type
{
    my $self = shift;
    if (@_) {
      $self->{outer_content_type} = shift;
    }
    return $self->{outer_content_type};
}
sub is_fatal_alert
{
    my $self = shift;
    my $server = shift;

    if (($self->{flight} & 1) == $server && $self->{content_type} == RT_ALERT) {
        my ($level, $description) = unpack('CC', $self->decrypt_data);
        return $description if ($level == 2);
    }
    return 0;
}
1;
