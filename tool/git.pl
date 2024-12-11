#!/usr/bin/env perl

use strict;
use warnings;

`sh ch.sh`;

print "\n******************************************\n";
print "* diff:\n";
print "******************************************\n";
print `git diff`;
print "******************************************\n\n";

my $n = `git diff | wc -l`;
chomp $n;

if ($n ne 0) {
  print "Please commit diffs!\n";
  exit 1;
}

my $s = `git log -1 | grep ^commit`;
chomp $s;
$s =~ s/^commit (........).*/$1/;

my $fc;
my $done = 0; # we want the commit after the last guilemacs commit
foreach my $line (`git log -10000`) {
  chomp $line;
  # keep track of the last commit
  if ($line =~ /^commit (........).*/) {
    $fc = $1;
    if ($done) {
      last;
    }
  }
  if ($line =~ /^\s*remove asynchronous input processing$/) {
    $done = 1;
  }
}

my $ad = `git show --format=%as $fc | head -1`;
chomp $ad;
$ad =~ s/-//g;

my $ver = `grep ^AC_INIT configure.ac`;
chomp $ver;
$ver =~ s/^AC_INIT..GNU Emacs., \[([^,]+)\],.*$/$1/;

print "$s $fc $ad $ver\n";
