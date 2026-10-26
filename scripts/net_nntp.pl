#!/usr/bin/env perl
# SPDX-License-Identifier: AGPL-3.0-or-later
# A client of the NNTP server written apart from it, for scripts/nntp_check.py: libnet's Net::NNTP, the
# version Perl ships, against the server on loopback at the port given, each wait at most TIMEOUT
# seconds. `reader TIMEOUT PORT ARTICLE...`: greeted as Net::NNTP connects, sending MODE READER, it posts
# each article, then asks DATE, the listings, GROUP, LISTGROUP, STAT, NEXT, LAST and ARTICLE of
# `local.test`. `refused TIMEOUT PORT`: MODE READER of a server without a store, then whether the
# connection was closed. Each answer is a line on stdout: what was asked, a tab, what Net::NNTP made of
# it; its conversation, each line it sent and each status line it read, is Net::Cmd's debugging on
# stderr.
use strict;
use warnings;
use IO::Select;
use Net::NNTP;

my ($mode, $timeout, $port, @articles) = @ARGV;
die "usage: net_nntp.pl reader TIMEOUT PORT ARTICLE... | refused TIMEOUT PORT\n"
  unless defined $port && ($mode eq 'reader' || ($mode eq 'refused' && !@articles));
die "this check needs Net::NNTP 3.15, not $Net::NNTP::VERSION\n" unless $Net::NNTP::VERSION eq '3.15';

sub answer { print join("\t", @_), "\n" }
sub given { defined $_[0] ? $_[0] : 'none' }

if ($mode eq 'refused') {
  my $news = Net::NNTP->new('127.0.0.1', Port => $port, Timeout => $timeout, Debug => 1, Reader => 0)
    or die "no connection: $@\n";
  $news->reader;
  answer('mode', $news->code);
  my $read = IO::Select->new($news)->can_read($timeout) ? sysread($news, my $byte, 1) : undef;
  answer('read', defined $read && $read == 0 ? 'closed' : 'open');
  exit 0;
}
my $news = Net::NNTP->new('127.0.0.1', Port => $port, Timeout => $timeout, Debug => 1)
  or die "no connection: $@\n";
answer('mode', $news->code);
answer('postok', $news->postok);
for my $file (@articles) {
  open(my $in, '<', $file) or die "$file: $!\n";
  my @lines = <$in>;
  close($in);
  $news->post(@lines);
  answer('post', $news->code);
}
my $when = $news->date;
answer('date', given($when));
for my $asked (['list', $news->list], ['active', $news->active('local.t*')],
               ['active-none', $news->active('*,!local.*')]) {
  my ($name, $groups) = @$asked;
  answer($name, $groups ? (map { join(' ', $_, @{$groups->{$_}}) } sort keys %$groups) : 'none');
}
for my $asked (['newsgroups', $news->newsgroups], ['newgroups', $news->newgroups(time - 86400)]) {
  my ($name, $groups) = @$asked;
  answer($name, $groups ? scalar keys %$groups : 'none');
}
answer('group', $news->group('local.test'));
my $numbers = $news->listgroup('local.test');
answer('listgroup', $numbers ? join(',', @$numbers) : 'none');
answer('stat', given($news->nntpstat(1)));
answer('next', given($news->next));
answer('next', given($news->next));
answer('last', given($news->last));
my $article = $news->article(2);
answer('article', $article ? unpack('H*', join('', @$article)) : 'none');
$news->quit;
answer('quit', $news->code);
