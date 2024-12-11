#!/usr/bin/perl

use strict;
use warnings;

my $earlier = $ARGV[0];
my $later  = $ARGV[1];

print `git rev-list --boundary 949d3e50..$later | grep -e $earlier -e $later`;
