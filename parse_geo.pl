#!/usr/bin/perl

use utf8;
use strict;
use warnings;
use open qw( :std :encoding(UTF-8) );
use List::Util qw(first);

sub analyze {
    open(my $fh, "<", "./Bet.thy")
	or die "error : $!";

    my @names;
    my %matrix;
    my %names;
    my $tek_name;
    
    my $i = 1;
    my $state = 0;
    while (<$fh>)
    {
	if ($_ =~ /^\s*lemma\s+(.*?):/) {
	    $names{$1} = 1;
	    push @names, $1;
	    $tek_name = $1;
	    
	    $state = 1;
	    print "$i ";
	    $i++;
	}
	elsif ($_ =~ /^\s*proof/) {
	    $state = 2;
	}

	if ($state == 1) {
	    my $str = $_;
	    $str =~ s/\\<Longrightarrow>/->/g;
	    $str =~ s/\<noteq>/≠/g;
	    
	    print $str;
	}
	elsif ($state == 2) {
	    if ($_ =~ /\bqed\b/) {
		$state = 0;
	    }
	    else {
		if ($_ =~ /\(rule\s+(.*)\s*\)/) {
		    if (exists $names{$1}) {
			if (exists $matrix{$tek_name}) {
			    unless (first { $_ eq $1} @{$matrix{$tek_name}}) {
				push @{$matrix{$tek_name}}, $1;
			    }
			}
			else {
			    $matrix{$tek_name} = [$1];
			}
		    }
		}
	    }
	}
    }

    print "\n";
    foreach (@names) {
	print "$_ : ";
	if (exists $matrix{$_}) {
	    my $n = scalar @{$matrix{$_}};
	    if ($n > 0) {
		for (my $i = 0; $i < $n - 1; ++$i)
		{
		    my $theorem = $matrix{$_}->[$i];
		    print "$theorem, ";
		}

		my $theorem = $matrix{$_}->[$n - 1];
		print "$theorem";
	    }
	}

	print "\n";
    }
    close $fh;
}

analyze();
