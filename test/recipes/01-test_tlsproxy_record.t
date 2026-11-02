#! /usr/bin/env perl
# Copyright 2026 The OpenSSL Project Authors. All Rights Reserved.
#
# Licensed under the Apache License 2.0 (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

=pod

=head1 NAME

01-test_tlsproxy_record.t - pure-Perl unit tests for the DTLS 1.3 unified header

=head1 DESCRIPTION

Drives L<TLSProxy::Record> directly: records are assembled by hand, pushed
through C<get_records()> and re-serialised with C<reconstruct_record()>.  No
s_server, no sockets, no C code, so a failure here points at the proxy itself.

The C<s_server> recipes cannot cover this.  Under a C<enable-dtls1_3_minunihdr>
build they only ever produce the C<S=0,L=0> header shape and the C<EE> values
C<10>/C<11>, so the branches added for C<S=1> and C<L=1> are never executed and
nothing exercises an epoch past 3.

=head2 Contract asserted here

The wire format of a record must be decided by the record itself, never by a
connection-scoped global, and the values the proxy reports must match what the
receiver computes:

=over 4

=item *

C<get_records()> records how the record arrived: C<unified()>,
C<unified_sbit()> and C<unified_lbit()>.  C<reconstruct_record()> branches on
C<unified()>, not on C<TLSProxy::Proxy-E<gt>is_tls13()> or C<encrypted()>.
The raw EE and sequence bits re-serialisation has to reproduce are not
asserted as accessors: the byte-exact round trips of section 1 are the
contract, and any way of keeping them satisfies it.

=item *

A unified header is DTLSCiphertext by definition, so it is de-protected
whenever it is parsed, whatever C<client_encrypting()> / C<server_encrypting()>
say at that moment.

=item *

C<new_dtls()> derives the format from C<epoch E<gt> 0>, mirroring
C<dtls_prepare_record_header()>.

=item *

C<epoch()> is the EE bits resolved against the direction's running epoch
(C<EE = epoch mod 4>, as C<dtls_prepare_record_header()> encodes it), and
C<seq()> is the full 64-bit number reconstructed from the direction's replay
window, ported from C<dtls13_reconstruct_seq_num()>.  Both are per direction and
per epoch, and C<TLSProxy::Record-E<gt>clear()> resets them, because
C<TLSProxy::Proxy-E<gt>clearClient()> calls it between connections.

=item *

A datagram too short to hold a unified header is reported as C<partial>; a
unified body below C<DTLS13_CIPHERTEXT_MINSIZE> + 1 bytes is dropped rather
than handed to C<decrypt()>; a CID (C) record is dropped rather than killing
the recipe.

=back

=cut

use strict;
use warnings;

use FindBin;
use File::Spec::Functions qw(catdir rel2abs);
use lib rel2abs(catdir($FindBin::Bin, '..', '..', 'util', 'perl'));

# Allow the recipe to be run directly, not just through "make test".
BEGIN {
    unless ($ENV{TOP} || ($ENV{SRCTOP} && $ENV{BLDTOP})) {
        $ENV{SRCTOP} = $ENV{BLDTOP}
            = rel2abs(catdir($FindBin::Bin, '..', '..'));
    }
}

use OpenSSL::Test;
use TLSProxy::Proxy;
use TLSProxy::Record;
use TLSProxy::Message;

setup('test_tlsproxy_record');

# Wire layout of a DTLS 1.3 unified header, from include/openssl/dtls1.h and
# ssl/record/methods/dtls_meth.c.
use constant UNI_FIX_MASK => 0xE0;
use constant UNI_FIX_BITS => 0x20;
use constant UNI_CID_BIT  => 0x10;
use constant UNI_SEQ_BIT  => 0x08;
use constant UNI_LEN_BIT  => 0x04;
use constant UNI_EE_MASK  => 0x03;

# DTLS13_CIPHERTEXT_MINSIZE (16 byte tag) plus the trailing content type byte.
use constant UNI_MIN_BODY => 17;
use constant TAG_LEN      => 16;

# The EE bits name the epoch modulo 4; the label in %record_type uses the
# RFC 9147 section 4.2.3 spelling of the same value.
my %EE_LABEL = (0 => 4, 1 => 1, 2 => 2, 3 => 3);

# ---------------------------------------------------------------- helpers ---

sub hx {
    return unpack('H*', $_[0] // '');
}

sub is_unified_byte {
    my ($byte) = @_;
    return defined $byte && length $byte == 1
           && (ord($byte) & UNI_FIX_MASK) == UNI_FIX_BITS;
}

sub uni_first {
    my ($s, $l, $ee) = @_;
    return UNI_FIX_BITS | ($s ? UNI_SEQ_BIT : 0)
                        | ($l ? UNI_LEN_BIT : 0) | ($ee & UNI_EE_MASK);
}

# Build a unified record body.  The first six bytes double as the sequence
# number mask (the ossltest engine makes the ECB encryption a no-op), so
# |mask| also controls what get_records() XORs back into the sequence number.
sub uni_body {
    my (%a) = @_;
    return $a{raw} if defined $a{raw};

    my $mask = defined $a{mask} ? $a{mask} : "\x41" x 6;
    my $ct   = defined $a{inner_ct} ? $a{inner_ct}
                                    : TLSProxy::Record::RT_APPLICATION_DATA();
    my $filler = defined $a{filler} ? $a{filler} : 20;

    return $mask . ("\x7f" x $filler) . chr($ct) . ("\0" x TAG_LEN);
}

# Assemble the on-the-wire bytes of one unified record.
sub uni_wire {
    my (%a) = @_;
    my $s    = $a{s}    // 0;
    my $l    = $a{l}    // 0;
    my $ee   = $a{ee}   // 2;
    my $seq  = $a{seq}  // 0;
    my $body = defined $a{body} ? $a{body} : uni_body();

    my $hdr = chr(uni_first($s, $l, $ee));
    $hdr .= $s ? pack('n', $seq & 0xffff) : pack('C', $seq & 0xff);
    $hdr .= pack('n', length $body) if $l;

    return $hdr . $body;
}

# Assemble the on-the-wire bytes of a legacy DTLSPlaintext record.  The default
# content type is application data because get_records() hands a handshake
# record on to TLSProxy::Message, which is not what these cases exercise.
sub legacy_wire {
    my (%a) = @_;
    my $body = defined $a{body} ? $a{body} : uni_body();

    return pack('Cnnnnnn', $a{content_type} // TLSProxy::Record::RT_APPLICATION_DATA(),
                $a{version} // TLSProxy::Record::VERS_DTLS_1_2(),
                $a{epoch} // 0, 0, 0, $a{seq} // 0, length $body) . $body;
}

# A body of exactly |$n| bytes.  A body long enough to be de-protectable puts
# a real content type where decrypt() expects it (just in front of the tag),
# so the "parsing is warning free" checks below only ever report proxy
# defects rather than artefacts of a synthetic body.
sub body_of_len {
    my ($n) = @_;
    return '' if $n <= 0;

    my $b = substr(("\0" x 6) . ("\x7f" x 40) . ("\0" x TAG_LEN), 0, $n);
    substr($b, $n - UNI_MIN_BODY, 1) = chr(TLSProxy::Record::RT_APPLICATION_DATA())
        if $n >= UNI_MIN_BODY;
    return $b;
}

# Run one datagram through get_records(), keeping its chatter out of the TAP
# stream.  Returns the records, the partial remainder, the printed dump and
# any warnings or exception text it produced.
sub parse {
    my (%a) = @_;

    TLSProxy::Record->clear() unless $a{keep_state};
    # Message state is per connection parser run, not the record state under
    # test, so it is always reset to keep the cases independent.
    TLSProxy::Message->clear();
    TLSProxy::Proxy->is_tls13($a{tls13} // 0);
    TLSProxy::Record->server_encrypting($a{server_enc} // 0);
    TLSProxy::Record->client_encrypting($a{client_enc} // 0);

    my $printed = '';
    my $warns   = '';
    my $xerr    = '';
    my ($recs, $msgs, $partial);

    my $cap;
    open($cap, '>', \$printed) or BAIL_OUT("cannot capture STDOUT: $!");
    my $old = select($cap);
    local $SIG{__WARN__} = sub { $warns .= $_[0] };
    eval {
        ($recs, $msgs, $partial) = TLSProxy::Record->get_records(
            $a{dir} // 1, $a{flight} // 1, $a{wire}, $a{isdtls} // 1);
        1;
    } or do { $xerr = $@ // 'died' };
    select($old);
    close($cap);

    return {
        recs    => $recs    // [],
        msgs    => $msgs    // [],
        partial => $partial // '',
        printed => $printed,
        warns   => $warns,
        xerr    => $xerr,
        died    => $xerr ne '',
    };
}

# Re-serialise one record, again with the chatter captured.
sub recon {
    my ($rec, $server) = @_;
    my $out  = '';
    my $xerr = '';

    return ('', 'no record') unless defined $rec;
    my $cap;
    open($cap, '>', \$out) or BAIL_OUT("cannot capture STDOUT: $!");
    my $old = select($cap);
    eval { $out = $rec->reconstruct_record($server); 1 }
        or do { $xerr = $@ // 'died'; $out = '' };
    select($old);
    close($cap);

    return ($out, $xerr);
}

# Read an accessor that a not-yet-implemented fix is expected to add, without
# taking the whole recipe down with it.
sub rec_attr {
    my ($rec, $name) = @_;
    return undef unless defined $rec && $rec->can($name);
    return $rec->$name;
}

sub negative_len_records {
    my ($recs) = @_;
    return [ grep { defined $_->len() && $_->len() < 0 } @{$recs} ];
}

# ------------------------------------------------- 1. header shape coverage ---

note('1. get_records() -> reconstruct_record() round trip for all 16 (S,L,EE) shapes');

for my $s (0, 1) {
    for my $l (0, 1) {
        for my $ee (0, 1, 2, 3) {
            my $wire = uni_wire(s => $s, l => $l, ee => $ee, seq => 0x34,
                                body => uni_body());
            my $r = parse(wire => $wire, dir => 1, flight => 1,
                          tls13 => 1, server_enc => 1);
            my ($got, $err) = recon($r->{recs}[0], 1);

            is(hx($got), hx($wire),
               sprintf('S=%d L=%d EE=%d round trips byte-exactly', $s, $l, $ee))
                or diag(sprintf('died=%s err=%s wire=%s got=%s',
                                $r->{died} ? 'yes' : 'no',
                                $err // $r->{xerr} // '',
                                hx($wire), hx($got)));
        }
    }
}

# The legacy path must keep working unchanged.
{
    my $wire = legacy_wire();
    my $r = parse(wire => $wire, dir => 1, flight => 1, tls13 => 1);
    my ($got) = recon($r->{recs}[0], 1);

    is(hx($got), hx($wire), 'legacy epoch-0 record round trips byte-exactly');
}

# ------------------------------------------------------- 2. %record_type ---

note('2. every unified first byte 0x20..0x2f is labelled with the right epoch');

for my $first (0x20 .. 0x2f) {
    my $s  = ($first & UNI_SEQ_BIT) ? 1 : 0;
    my $l  = ($first & UNI_LEN_BIT) ? 1 : 0;
    my $ee = $first & UNI_EE_MASK;
    my $body = uni_body();
    my $wire = uni_wire(s => $s, l => $l, ee => $ee, seq => 0x34, body => $body);

    my $r = parse(wire => $wire, dir => 1, flight => 1,
                  tls13 => 1, server_enc => 1);
    my ($label) = $r->{printed} =~ /^ *Content type: (.*)$/m;

    is($label, sprintf('DTLS UNIFIED HEADER (EPOCH %d)', $EE_LABEL{$ee}),
       sprintf('first byte 0x%02x (S=%d L=%d EE=%d) is labelled correctly',
               $first, $s, $l, $ee));
}

# The RT_DTLS_UNIHDR_EPOCH* constants are matched on by recipes, so generating
# the label table must not move them.  Note they only name the S=1,L=1 forms.
is(TLSProxy::Record::RT_DTLS_UNIHDR_EPOCH4(), 0x2c,
   'RT_DTLS_UNIHDR_EPOCH4 still names 0x2c');
is(TLSProxy::Record::RT_DTLS_UNIHDR_EPOCH1(), 0x2d,
   'RT_DTLS_UNIHDR_EPOCH1 still names 0x2d');
is(TLSProxy::Record::RT_DTLS_UNIHDR_EPOCH2(), 0x2e,
   'RT_DTLS_UNIHDR_EPOCH2 still names 0x2e');
is(TLSProxy::Record::RT_DTLS_UNIHDR_EPOCH3(), 0x2f,
   'RT_DTLS_UNIHDR_EPOCH3 still names 0x2f');

# ------------------------------------- 3. the format follows the record ---

note('3. a unified record stays unified regardless of connection state');

{
    # The clearClient() scenario: a stray post-handshake record is stamped
    # flight 0 of the next connection while is_tls13() is already back to 0.
    # client_encrypting is set here so this case isolates the format decision
    # from the decrypt gate, which section 4 covers.
    my $body = uni_body(inner_ct => TLSProxy::Record::RT_ALERT());
    my $wire = uni_wire(s => 0, l => 0, ee => 3, seq => 0x03, body => $body);
    my $r = parse(wire => $wire, dir => 0, flight => 0,
                  tls13 => 0, client_enc => 1);
    my ($got, $err) = recon($r->{recs}[0], 0);

    # The legacy encoder also writes the outer content type as its first byte,
    # so only the header size tells the two shapes apart.
    is(length($got) - length($body), 2,
       'unified record parsed while is_tls13()==0 keeps a 2-byte unified header')
        or diag(sprintf('got %d bytes for a %d byte body, first byte %s, err %s',
                        length($got), length($body),
                        length($got) ? sprintf('0x%02x', ord(substr($got, 0, 1)))
                                     : '<none>',
                        $err // ''));
    is(hx($got), hx($wire),
       'unified record parsed while is_tls13()==0 round trips byte-exactly');
}

# ------------------------------------------- 4. unified is always decrypted ---

note('4. a unified record is de-protected even while the connection is not encrypting');

{
    my $body = uni_body(inner_ct => TLSProxy::Record::RT_APPLICATION_DATA());

    # Already the case today: is_tls13() carries the decrypt gate.
    my $r = parse(wire => uni_wire(s => 0, l => 0, ee => 2, seq => 0x02,
                                   body => $body),
                  dir => 0, flight => 0, tls13 => 1);
    is(rec_attr($r->{recs}[0], 'encrypted'), 1,
       'unified record with is_tls13()==1 and client_encrypting()==0 is de-protected');
    is($r->{recs}[0]->content_type(), TLSProxy::Record::RT_APPLICATION_DATA(),
       '...and its inner content type is revealed');

    # The defect: a 0-RTT record, or a keyed record buffered behind an epoch-0
    # flight, arrives before the ServerHello sets both globals.
    $r = parse(wire => uni_wire(s => 0, l => 0, ee => 2, seq => 0x02,
                                body => $body),
               dir => 0, flight => 0, tls13 => 0);
    is(rec_attr($r->{recs}[0], 'encrypted'), 1,
       'unified record with is_tls13()==0 and client_encrypting()==0 is de-protected');

    # A unified header is never a plaintext alert, so the TLS 1.3
    # "2-byte alert" escape in decrypt() must not be reachable for one.
    $r = parse(wire => uni_wire(s => 0, l => 0, ee => 2, seq => 0x02,
                                body => $body),
               dir => 1, flight => 1, tls13 => 1);
    isnt($r->{recs}[0]->content_type(), 0x22,
         'a unified record is never left carrying its raw outer content type');
}

# ------------------------------------- 5. records injected by a test ---

note('5. new_dtls() picks the format from the epoch, not from encrypted()');

{
    # A DTLS handshake message header: type, 24-bit length, message sequence,
    # 24-bit fragment offset, 24-bit fragment length.
    my $hm = pack('C', 1) . pack('C3', 0, 0, 0) . pack('n', 9)
           . pack('C3', 0, 0, 0) . pack('C3', 0, 0, 0);

    TLSProxy::Record->clear();
    TLSProxy::Proxy->is_tls13(1);
    my $rec = TLSProxy::Record->new_dtls(1, 5, TLSProxy::Record::RT_HANDSHAKE(),
                                         TLSProxy::Record::VERS_DTLS_1_2(),
                                         3, 7, length($hm), length($hm),
                                         length($hm), $hm, $hm);
    my ($got, $err) = recon($rec, 1);

    ok(is_unified_byte(length($got) ? substr($got, 0, 1) : undef),
       'new_dtls(epoch => 3) is serialised as DTLSCiphertext')
        or diag(sprintf('got %d bytes, first byte %s, err %s',
                        length($got),
                        length($got) ? sprintf('0x%02x', ord(substr($got, 0, 1)))
                                     : '<none>',
                        $err // ''));
    cmp_ok(length($got), '<', 13 + length($hm),
           '...and not with the 13-byte DTLSPlaintext header the peer discards');

    # Epoch 0 stays DTLSPlaintext: that is the library rule at
    # dtls_prepare_record_header(), and the hellos depend on it.
    TLSProxy::Record->clear();
    TLSProxy::Proxy->is_tls13(1);
    my $rec0 = TLSProxy::Record->new_dtls(1, 1, TLSProxy::Record::RT_HANDSHAKE(),
                                          TLSProxy::Record::VERS_DTLS_1_2(),
                                          0, 0, length($hm), length($hm),
                                          length($hm), $hm, $hm);
    my ($got0) = recon($rec0, 1);

    is(substr($got0, 0, 1), chr(TLSProxy::Record::RT_HANDSHAKE()),
       'new_dtls(epoch => 0) keeps the legacy DTLSPlaintext content type');
    is(length($got0), 13 + length($hm),
       '...with the full 13-byte legacy header');
}

# --------------------------------- 6. truncated and short unified records ---

note('6. truncated and short unified records are rejected, not parsed as garbage');

{
    my @cases;

    # Too short to hold the header itself: the datagram has to come back as
    # partial, the way the legacy path already reports truncation.
    foreach my $t ([0, 0], [1, 0], [0, 1], [1, 1]) {
        my $wire = chr(uni_first($t->[0], $t->[1], 3));
        push @cases, { label => sprintf('1-byte header, S=%d L=%d', @{$t}),
                       wire => $wire, recs => 0, partial => $wire };
    }
    # Complete header, body too short to hold an AEAD tag plus the trailing
    # content type byte, so decrypt() would be handed a negative length.
    my $l0 = chr(uni_first(0, 0, 3));
    my $l1 = chr(uni_first(0, 1, 3));
    foreach my $n (0, 5, UNI_MIN_BODY - 1) {
        push @cases, { label => "L=0 body of $n bytes",
                       wire => $l0 . chr(0x00) . body_of_len($n),
                       recs => 0 };
    }
    push @cases, { label => 'L=1 body of 5 bytes',
                   wire => $l1 . chr(0x00) . pack('n', 5) . body_of_len(5),
                   recs => 0 };
    # The smallest body the receiver will accept.  Its de-protected payload is
    # empty, which trips the proxy's own debug print rather than the parser, so
    # the warning check moves to a body with actual payload behind the tag.
    push @cases, { label => 'L=0 body of ' . UNI_MIN_BODY . ' bytes',
                   wire => $l0 . chr(0x00) . body_of_len(UNI_MIN_BODY),
                   recs => 1, nowarn => 0 };
    push @cases, { label => 'L=0 body of 24 bytes',
                   wire => $l0 . chr(0x00) . body_of_len(24),
                   recs => 1 };

    foreach my $c (@cases) {
        my $r = parse(wire => $c->{wire}, dir => 1, flight => 1,
                      tls13 => 1, server_enc => 1);

        is(scalar @{$r->{recs}}, $c->{recs},
           sprintf('%s: %d record(s)', $c->{label}, $c->{recs}));
        is(scalar @{negative_len_records($r->{recs})}, 0,
           sprintf('%s: no record with a negative length', $c->{label}));
        is($r->{warns}, '', sprintf('%s: parsing is warning free', $c->{label}))
            or diag($r->{warns})
            if $c->{nowarn} // 1;
        is($r->{partial}, $c->{partial} // '',
           sprintf('%s: %s', $c->{label},
                   defined $c->{partial} ? 'truncated datagram returned as partial'
                                         : 'nothing left as partial'))
            if exists $c->{partial};
    }

    # The legacy path already reports truncation through partial; the unified
    # checks above must not change that.
    my $trunc = pack('Cnnnnn', TLSProxy::Record::RT_HANDSHAKE(),
                     TLSProxy::Record::VERS_DTLS_1_2(), 0, 0, 0);
    my $r = parse(wire => $trunc, dir => 1, flight => 1, tls13 => 1);
    is(scalar @{$r->{recs}}, 0, 'truncated legacy header yields no record');
    is($r->{partial}, $trunc, '...and is returned as partial');

    $r = parse(wire => '', dir => 1, flight => 1, tls13 => 1);
    is(scalar @{$r->{recs}}, 0, 'empty datagram yields no record');
    ok(!$r->{died}, 'empty datagram does not abort the recipe');
}

# ------------------------------------------------- 7. connection ID ---

note('7. a CID unified record is dropped, not fatal');

{
    my $wire = chr(uni_first(0, 0, 3) | UNI_CID_BIT) . chr(0x00) . uni_body();
    my $r = parse(wire => $wire, dir => 1, flight => 1,
                  tls13 => 1, server_enc => 1);

    # One assertion, because "no record" on its own is also what a die()
    # produces, and die() is precisely the behaviour being replaced.
    ok(!$r->{died} && @{$r->{recs}} == 0,
       'a unified record with the C bit set is dropped instead of killing the recipe')
        or diag($r->{died} ? 'died with: ' . ($r->{xerr} // '')
                           : 'parsed ' . scalar(@{$r->{recs}}) . ' record(s)');
}

# ------------------------------- 8. epoch and sequence number reconstruction ---

note('8. EE bits resolve to the real epoch and sequence numbers are reconstructed');

{
    # Epochs past 4 only appear after a KeyUpdate; the wire carries epoch mod 4
    # so the proxy has to resolve it against what it has already seen from
    # this direction.
    TLSProxy::Record->clear();
    TLSProxy::Message->clear();
    TLSProxy::Proxy->is_tls13(1);
    TLSProxy::Record->server_encrypting(1);

    my @seen;
    for my $epoch (1 .. 8) {
        my $wire = uni_wire(s => 0, l => 0, ee => $epoch & 3,
                            seq => ($epoch * 3) & 0xff,
                            body => uni_body());
        my $r = parse(keep_state => 1, wire => $wire, dir => 1, flight => 1,
                      tls13 => 1, server_enc => 1);
        push @seen, defined $r->{recs}[0] ? $r->{recs}[0]->epoch() : undef;
    }
    is_deeply(\@seen, [1 .. 8],
              'EE bits resolve to epochs 1..8, not to the mod-4 table')
        or diag('observed: ' . join(',', map { $_ // 'undef' } @seen));
}

{
    # One epoch has to carry more than 256 records; with S=0 the wire only
    # carries eight of them.  A zero mask makes the wire value the truncated
    # sequence number, so the expectation is simply the counter itself.
    TLSProxy::Record->clear();
    TLSProxy::Message->clear();
    TLSProxy::Proxy->is_tls13(1);
    TLSProxy::Record->server_encrypting(1);

    my $body = uni_body(mask => "\0" x 6);
    my @seen;
    for my $i (0 .. 260) {
        my $wire = uni_wire(s => 0, l => 0, ee => 2, seq => $i & 0xff,
                            body => $body);
        my $r = parse(keep_state => 1, wire => $wire, dir => 1, flight => 1,
                      tls13 => 1, server_enc => 1);
        push @seen, defined $r->{recs}[0] ? $r->{recs}[0]->seq() : undef;
    }
    is_deeply(\@seen, [0 .. 260],
              'sequence numbers past 255 are reconstructed from the replay window')
        or do {
            my ($bad) = grep { $seen[$_] != $_ } 0 .. $#seen;
            diag(defined $bad
                 ? sprintf('first divergence at record %d: expected %d, observed %s',
                           $bad, $bad, $seen[$bad] // 'undef')
                 : 'no records parsed');
        };
}

{
    # The replay window and the running epoch are per direction and per epoch:
    # neither may inherit the other direction's, or the other epoch's, counter.
    TLSProxy::Record->clear();
    TLSProxy::Message->clear();
    TLSProxy::Proxy->is_tls13(1);
    TLSProxy::Record->server_encrypting(1);
    TLSProxy::Record->client_encrypting(1);

    my $body = uni_body(mask => "\0" x 6);
    for my $i (0 .. 260) {
        parse(keep_state => 1, dir => 1, flight => 1, tls13 => 1,
              server_enc => 1,
              wire => uni_wire(s => 0, l => 0, ee => 2, seq => $i & 0xff,
                               body => $body));
    }

    my $r = parse(keep_state => 1, dir => 1, flight => 1, tls13 => 1,
                  server_enc => 1,
                  wire => uni_wire(s => 0, l => 0, ee => 3, seq => 5,
                                   body => $body));
    is(defined $r->{recs}[0] ? $r->{recs}[0]->seq() : undef, 5,
       'a new epoch starts its own replay window instead of continuing the old one');

    $r = parse(keep_state => 1, dir => 0, flight => 0, tls13 => 1,
               client_enc => 1,
               wire => uni_wire(s => 0, l => 0, ee => 2, seq => 5, body => $body));
    is(defined $r->{recs}[0] ? $r->{recs}[0]->seq() : undef, 5,
       'the other direction starts its own replay window too');
}

# ------------------------------------- 9. the record carries its own format ---

note('9. the record records how it arrived instead of inheriting it from globals');

{
    my $r = parse(wire => uni_wire(s => 1, l => 0, ee => 2, seq => 0x1234,
                                   body => uni_body()),
                  dir => 1, flight => 1, tls13 => 1, server_enc => 1);
    my $rec = $r->{recs}[0];

    is(scalar @{$r->{recs}}, 1, 'unified datagram parsed into one record');
    is(rec_attr($rec, 'unified'), 1, 'which reports itself as unified()');
    is(rec_attr($rec, 'unified_sbit'), 1, '...and unified_sbit()');
    is(rec_attr($rec, 'unified_lbit'), 0, '...and unified_lbit()');

    # A legacy record must say so too, or reconstruct_record() has nothing to
    # branch on once is_tls13() stops being the input.  The raw EE and
    # sequence bits re-serialisation needs are not asserted as accessors: the
    # byte-exact round trips in section 1 are the contract, and they hold for
    # any way of keeping them.
    $r = parse(wire => legacy_wire(), dir => 1, flight => 1, tls13 => 1);
    is(scalar @{$r->{recs}}, 1, 'legacy datagram parsed into one record');
    is(rec_attr($r->{recs}[0], 'unified'), 0,
       'which reports itself as not unified');
}

done_testing();
