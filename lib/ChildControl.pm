package ChildControl;

use strict;
use warnings;
use Carp;
use IO::Handle;

=pod

=head1 NAME

ChildControl - Controlled start of a child process.

=head1 SYNOPSIS

  Quick code sample should go here...

=head1 METHODS

The methods for this module are listed here:

=over 4

=cut

#============================================================================#

=pod

=item I<Public>: B<start_child>

Currently undocumented.

=cut

sub start_child {
  my $self = shift;

  ($$ == $self->{__pid}) or
    croak ("start_child called from non-parent process");

  close $self->{__read} or
    croak ("Failed to close read side of pipe in parent: $!");

  my $write = $self->{__write};
  print $write "GO";
  close $self->{__write} or
    croak ("Failed to close write side of pipe in parent: $!");
}

#========================================================================#

=pod

=item I<Public>: B<wait_for_parent>

Currently undocumented.

=cut

sub wait_for_parent {
  my $self = shift;

  ($$ != $self->{__pid}) or
    croak ("wait_for_parent called in parent process");

  close $self->{__write} or
    croak ("Failed to close write side of pipe in child: $!");

  my $go_text = undef;
  read $self->{__read}, $go_text, 2 or
    croak ("Failed to read from pipe: $!");

  ((defined $go_text) and ($go_text eq "GO")) or
    croak ("Unexpected text on pipe");

  close $self->{__read} or
    croak ("Failed to close read side of pipe in child: $!");
}

#========================================================================#

=pod

=item I<Public>: B<new>

Create a new instance of ChildControl and then call initialise
on it.

=cut

sub new {
  my $class = shift;

  #-----------------------------#
  # Don't change this method    #
  # Change 'initialise' instead #
  #-----------------------------#

  my $self  = bless {}, $class;
  $self->initialise(@_);
  return $self;
}

#============================================================================#

=pod

=item I<Private>: B<initialise>

Initialise this instance of this class.

=cut

sub initialise {
  my $self = shift;
  my %args = @_;

  $self->{__pid} = $$;
  my ($read, $write);

  pipe $read, $write or
    croak ("Failed to create pipe: $!");

  $write->autoflush ();
  $self->{__read} = $read;
  $self->{__write} = $write;
}

#============================================================================#

=pod

=back

=head1 AUTHOR

Andrew Burgess, 11 Jan 2016

=cut

#============================================================================#
#Return value of true so that this file can be used as a module.
1;
