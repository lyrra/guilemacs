#!/usr/bin/perl

foreach my $tag (`git tag`) {
  chomp $tag;
  next if ((!($tag =~ /^r\d/)) and
           (!($tag =~ /\d\d.\d+.\d+-\d{8}-\d{8}/)));
  print "[$tag]\n";
  print `git push cb tag $tag`;
}
