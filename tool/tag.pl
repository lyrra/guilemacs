#!/usr/bin/perl

my $dry_run = 0;

my $n = 0;

foreach my $arg (@ARGV) {
  if ($arg eq "--dry-run") {
    $dry_run = 1;
  } else {
    $n = $arg;
  }
}

die "need to set start commit-index!" if ! $n;

while(my $line = <STDIN>) {
  chomp $line;
  next if $line eq "";
  next if $line =~ /^[!#\+-]/;
  my ($commit, $rest) = ($line =~ /^(\w+)(.*)/);
  $rest =~ s/^\s*//g;
  $rest =~ s/\s/-/g;
  $rest =~ s/#.*$//;
  $rest = "r$n-$rest";
  $rest =~ s/-+$//g;
  print "$commit [$rest]\n";
  # remark this line to dry-run
  if (! $dry_run) {
    print `git tag $rest $commit`;
  }
  $n++;
}
