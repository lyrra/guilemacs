#!/usr/bin/perl

use strict;
use warnings;

my @tmp = `find prelude mod src lib-src lwlib lisp | grep -e '\\.c\$' -e '\\.h\$' -e '\\.el\$' -e '\\.scm\$'`;

my $elcnt = 0;
my $chcnt = 0;
my $scmcnt = 0;

foreach my $file (@tmp) {
  chomp $file;
  if ($file =~ /\.el$/) {
    my ($cnt) = (`wc -l $file` =~ /^(\d+)\s+.*/);
    $elcnt += $cnt;
  } elsif ($file =~ /\.[ch]$/) {
    my ($cnt) = (`wc -l $file` =~ /^(\d+)\s+.*/);
    $chcnt += $cnt;
  } elsif ($file =~ /\.scm$/) {
    my ($cnt) = (`wc -l $file` =~ /^(\d+)\s+.*/);
    $scmcnt += $cnt;
  }
}

my $tot = $elcnt + $chcnt + $scmcnt;
my $pelcnt = $elcnt / $tot * 100;
my $pchcnt = $chcnt / $tot * 100;
my $pscmcnt = $scmcnt / $tot * 100;

printf "total  elisp: $elcnt  (%8f)\n", $pelcnt;
printf "total    c/h: $chcnt  (%8f)\n", $pchcnt;
printf "total scheme: $scmcnt  (%8f)\n", $pscmcnt;
printf "total       : $tot\n";
