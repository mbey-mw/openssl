#! /usr/bin/env perl
# Copyright 2026 The OpenSSL Project Authors. All Rights Reserved.
#
# Licensed under the Apache License 2.0 (the "License").  You may not use
# this file except in compliance with the License.  You can obtain a copy
# in the file LICENSE in the source distribution or at
# https://www.openssl.org/source/license.html

# DTLS 1.3 record-manipulation cases for TLSProxy.
#
# These are the DTLS 1.3 counterparts of the subtests that
# 70-test_sslrecords.t skips with "Record tests not intended for dtls", plus a
# KeyUpdate-driven case.  They belong here rather than in that recipe because
# the unified header changes what "the record type" and "a record boundary"
# even mean: with L=0 the first byte is the header and the datagram boundary is
# the only record boundary the peer can see.
#
# The KeyUpdate cases are the reason this file exists.  Epochs past 4 only
# occur after a KeyUpdate, and until now nothing but the pure-Perl recipe
# 01-test_tlsproxy_record.t ever produced one, which is how both the wrong
# EE-bits table and the absent sequence-number reconstruction survived: on the
# traffic that was ever generated, each wrong reading happened to agree with
# the right one.  s_server calls SSL_key_update() when it reads "k" or "K" on
# its stdin, and the proxy holds that stdin open on a pipe, so the test can
# drive it directly.

use strict;
use OpenSSL::Test qw/:DEFAULT cmdstr srctop_file bldtop_dir/;
use OpenSSL::Test::Utils;
use TLSProxy::Proxy;
use TLSProxy::Record;
use TLSProxy::Message;
use Cwd qw(abs_path);

my $test_name = "test_dtls13records";
setup($test_name);

plan skip_all => "TLSProxy isn't usable on $^O"
    if $^O =~ /^(VMS)$/ || $^O =~ /^(MSWin32)$/;

plan skip_all => "$test_name needs the module feature enabled"
    if disabled("module");

plan skip_all => "$test_name needs the sock feature enabled"
    if disabled("sock");

plan skip_all => "$test_name needs DTLSv1.3 enabled"
    if disabled("dtls1_3");

plan skip_all => "DTLSProxy does not support partial messages"
    if disabled("ec");

$ENV{OPENSSL_MODULES} = abs_path(bldtop_dir("test"));

my $proxy = TLSProxy::Proxy->new_dtls(
    undef,
    cmdstr(app(["openssl"]), display => 1),
    srctop_file("apps", "server.pem"),
    (!$ENV{HARNESS_ACTIVE} || $ENV{HARNESS_VERBOSE}),
    have_IPv6()
);

my $testcount = 5;
plan tests => $testcount;

my $keyupdate_count = 0;
my $keyupdate_sent = 0;
my $keyupdate_min_flight = 5;
my $filter_calls;
my $want_epoch;
my $max_server_epoch;
my $phase;
my $server_epochs_seen;
my $saw_traffic;
my $saw_client_finished;

sub set_up
{
    my (%a) = @_;

    $proxy->clear();
    $server_epochs_seen = [];
    $saw_traffic = 0;
    $saw_client_finished = 0;
    $keyupdate_count = $a{keyupdates} // 0;
    $keyupdate_sent = 0;
    $keyupdate_min_flight = $a{keyupdate_from} // 5;
    $filter_calls = 0;
    $want_epoch = $a{want_epoch};
    $max_server_epoch = undef;
    $phase = 0;
    $proxy->filter($a{filter});
    # Every case here needs the client alive past the handshake, which the
    # proxy's usual "close the client's stdin once the request is queued" would
    # end.  drive_rekey() hangs it up again when the run has what it came for.
    $proxy->hold_client_stdin(1);
    $proxy->serverflags("-min_protocol DTLSv1.3 -max_protocol DTLSv1.3");
    $proxy->clientflags("-min_protocol DTLSv1.3 -max_protocol DTLSv1.3"
                        ." -groups ?X25519:?P-256");
    # successondata stays off: the proxy would otherwise leave the pump loop as
    # soon as the request data and the session tickets are through, which is
    # long before any of the rekeying happens.
    TLSProxy::Message->successondata($a{successondata} // 0);
}

# Records are observed from the filter, which runs once per datagram before
# anything has been marked sent, so the scan is cumulative over every flight
# seen so far.
sub scan_records
{
    my $inproxy = shift;

    foreach my $record (@{$inproxy->record_list}) {
        next unless $record->serverissender();

        $saw_traffic = 1;
        my $epoch = $record->epoch();
        push @{$server_epochs_seen} => $epoch
            unless grep { $_ == $epoch } @{$server_epochs_seen};
        $max_server_epoch = $epoch
            if !defined($max_server_epoch) || $epoch > $max_server_epoch;
    }

    # The client only answers with its Finished once it has accepted every
    # protected record we forwarded it, so this is the proxy-side witness that
    # the peer took the server's flight.  When a record is discarded the client
    # goes quiet and s_server just retransmits instead.
    foreach my $message (@{$inproxy->message_list}) {
        $saw_client_finished = 1
            if !$message->server()
               && $message->mt() == TLSProxy::Message::MT_FINISHED;
    }
}

# Drive the rekeying, one step per datagram so each has time to round-trip.
#
# Phase 0 asks s_server for KeyUpdates by writing to the stdin the proxy holds
# open for it (apps/s_server.c reacts to a line holding just "k" by calling
# SSL_key_update() and then SSL_do_handshake()), one per datagram until the
# epoch under test shows up.  They have to go out one at a time, and they have
# to keep coming: a single SSL_do_handshake() does not finish a DTLS 1.3
# post-handshake flight, it returns -1 waiting for the peer's ACK, and s_server
# does not call it again until the next command arrives -- so the next "k" is
# also what drives the previous KeyUpdate out.  That matters for what is being
# measured, because the KeyUpdate record itself is written in the *old* epoch:
# tls13_update_key(), which is what bumps w_conn_epoch, runs in the state
# machine's post-state (statem_srvr.c TLS_ST_SW_KEY_UPDATE), so only the records
# after it carry the new epoch.
#
# Phase 1 has the client ask for a reply, so the newest epoch also carries
# ordinary application data and not just another KeyUpdate.  Phase 2 hangs up
# the client's stdin; s_client then sends its close_notify, which is what lets
# both apps and the pump loop finish.
sub drive_rekey
{
    my $inproxy = shift;

    $filter_calls++;

    if ($phase == 0) {
        my $reached = defined($want_epoch) && defined($max_server_epoch)
                      && $max_server_epoch >= $want_epoch;
        my $exhausted = $keyupdate_sent >= $keyupdate_count;
        # A run whose records are being discarded never gets past the server's
        # first flight, it just watches s_server retransmit, so the wind-down
        # cannot be gated on the flight number alone -- that leaves the pump
        # loop to idle out, and that path kills s_server with SIGQUIT and the
        # teardown dies on the exit status.  The cap is generous for the
        # rekeying runs, which need dozens of datagrams to climb an epoch.
        my $stalled = $filter_calls > ($keyupdate_count > 0 ? 60 : 8);

        return if $inproxy->flight < $keyupdate_min_flight && !$stalled;
        if ($reached || $exhausted || $stalled) {
            $phase = 1;
        } else {
            $keyupdate_sent++;
            $inproxy->write_to_server_stdin("k\n");
            return;
        }
    }
    if ($phase == 1) {
        $inproxy->write_to_client_stdin("more\n");
        $phase = 2;
        return;
    }
    return if $phase > 2;
    $inproxy->close_client_stdin();
    $phase = 3;
}

# The record-manipulation filters below rewrite the first byte of the protected
# records the server sends.  They have to keep doing it: tampering one
# transmission only delays the client, because s_server retransmits the flight
# and the retransmission, arriving as a fresh datagram, is parsed clean and
# accepted.
my $tampered;

# DTLS 1.3 counterpart of 70-test_sslrecords.t's "Wrong outer record type in
# TLS1.3", which is one of the subtests that recipe skips for DTLS.
#
# For a unified record the "outer content type" is not a content type at all:
# the first byte *is* the header, and its fix bits are load-bearing -- RFC 9147
# s4.2.3 gives the peer no way to recognise the datagram once they are gone.
# Rewriting it to a TLS content type is therefore not a rename, it is a
# malformed record, and the peer has to discard it.
sub change_outer_content_type
{
    my $inproxy = shift;

    return if $inproxy->flight < 3;
    foreach my $record (@{$inproxy->record_list}) {
        next if $record->{tampered}
                || !$record->serverissender()
                || !$record->unified();

        $record->outer_content_type(TLSProxy::Record::RT_HANDSHAKE);
        $record->{tampered} = 1;
        $tampered = 1;
    }
}

# The unified header has no version field to corrupt, so the epoch bits are
# where a lie about a protected record has to go.  Claiming EE=00 for a record
# the server actually wrote under a later key sends the peer to the wrong
# record layer, which is the DTLS 1.3 shape of the "changed record version"
# subtest.
sub change_epoch_bits
{
    my $inproxy = shift;

    return if $inproxy->flight < 3;
    foreach my $record (@{$inproxy->record_list}) {
        next if $record->{tampered}
                || !$record->serverissender()
                || !$record->unified();

        my $first = $record->outer_content_type();
        $record->outer_content_type(($first & 0xfc) | 0x00);
        $record->{tampered} = 1;
        $tampered = 1;
    }
}

# --------------------------------------------------------------------------
# Tests 1 and 2: repeated KeyUpdates from s_server have to take the server's
# epoch past 4, and the proxy has to report the resolved epoch rather than
# replaying the RFC 9147 section 4.2.3 table.
#
# Epoch 4 goes on the wire as EE=00, which that table also happens to call 4,
# so test 1 alone would not notice the wrong table.  Epoch 5 is EE=01, which
# that table calls 1: it is the case that discriminates, and the reason this
# recipe exists.  Confirmed by reverting resolve_epoch() to that table: test 2
# then reports "epochs seen: 0,2,3,4,1" and fails, while test 1 still passes.
# --------------------------------------------------------------------------

set_up(keyupdates => 8, want_epoch => 4,
       filter => sub { scan_records(@_); drive_rekey(@_); });
SKIP: {
    skip "TLSProxy could not start", 2 if !$proxy->start() && !$saw_traffic;

    my %seen = map { $_ => 1 } @{$server_epochs_seen};
    ok($seen{4}, "Rekeying takes the server into epoch 4")
        or diag('epochs seen: ' . join(',', @{$server_epochs_seen}));
}

set_up(keyupdates => 14, want_epoch => 5,
       filter => sub { scan_records(@_); drive_rekey(@_); });
$proxy->start();

{
    my %seen = map { $_ => 1 } @{$server_epochs_seen};
    ok($seen{5}, "Rekeying takes the server into epoch 5, whose EE bits 01 the"
                ." RFC 9147 table misreads as 1")
        or diag('epochs seen: ' . join(',', @{$server_epochs_seen}));

    # Control for tests 4 and 5, which pass by *not* seeing this.  Without it
    # they would pass just as happily on a run where the client never got
    # anywhere at all.
    ok($saw_client_finished,
       "Control: an untampered run gets a Finished from the client")
        or diag('the client never answered with a Finished');
}

# --------------------------------------------------------------------------
# Tests 3 and 4: the record-manipulation cases from 70-test_sslrecords.t that
# have a DTLS 1.3 meaning.  Those subtests are skipped for DTLS there, which is
# how the injected-record defects survived: an injected or rewritten record used
# to be silently discarded by the peer and the test still passed, so it asserted
# nothing.  Each one therefore checks the tampering really happened as well as
# the reaction to it.
#
# The rest of the skipped group has no DTLS 1.3 counterpart: tests 7, 8 and 16
# change the record *version* field, which a unified header does not serialise
# at all, and the record-boundary cases 11-15 turn on fragmentation and
# coalescing inside one stream, which under MINUNIHDR is settled by the
# datagram boundary -- covered by 70-test_dtls13ack.t test 5.
# --------------------------------------------------------------------------

$tampered = 0;
set_up(filter => sub { scan_records(@_);
                       change_outer_content_type(@_);
                       drive_rekey(@_); });
SKIP: {
    skip "TLSProxy could not start", 2 if !$proxy->start() && !$saw_traffic;

    ok($tampered && !$saw_client_finished,
       "A unified record whose first byte has lost its fix bits is discarded")
        or diag('tampered: '.($tampered // 0)
                .' client answered Finished: '.$saw_client_finished);
}

$tampered = 0;
set_up(filter => sub { scan_records(@_);
                       change_epoch_bits(@_);
                       drive_rekey(@_); });
SKIP: {
    skip "TLSProxy could not start", 2 if !$proxy->start() && !$saw_traffic;

    ok($tampered && !$saw_client_finished,
       "A unified record that lies about its epoch bits is discarded")
        or diag('tampered: '.($tampered // 0)
                .' client answered Finished: '.$saw_client_finished);
}
