#!/usr/bin/perl

use warnings;
use strict;

#========================================================================#

=pod

=head1 NAME

run-tests - a quick summary of what run-tests does.

=head1 OPTIONS

  B<run-tests> [--help | -h]
               --sim-count=COUNT
               --sim-log-directory=SIM-LOG-DIR
               --gcc-build-directory=GCC-BUILD-DIR
               --gcc-src-directory=GCC-SRC-DIR
               --results-directory=RESULT-DIR
               --test-list=TEST-LIST-FILE
               --ezdk-directory=EZDK-DIR
               [ --max-test-attempts=NUMBER ]

=head1 SYNOPSIS

A full description for run-tests has not yet been written.

=over 2

=item B<--help> | B<-h>

Produce this help text and exit.

=item B<--sim-count>=I<COUNT>

Run at most I<COUNT> simulators.  Default to 1.

=item B<--sim-log-directory>=I<SIM-LOG-DIR>

A directory, that must already exist, into which the simulator log
files are produced.

=item B<--gcc-build-directory>=I<GCC-BUILD-DIR>

Location of the GCC build tree, needed to locate the site.exp file within
the build tree.

=item B<--gcc-src-directory>=I<GCC-SRC-DIR>

Location of the GCC souce tree, used to locate the gcc testsuite
source.

=item B<--results-directory>=I<RESULT-DIR>

Directory into which results will be generated.

=item B<--test-list>=I<TEST-LIST-FILE>

File containing the list of the tests to run.  See the I<TEST-LIST-FILE>
section below for details on the format of this file.

=item B<--ezdk-directory>=I<EZDK-DIR>

The location of the EZdk directory, this is the unpacked EZChip SDK.
This is used as the location of the simulator.

=item B<--max-test-attempts>=I<NUMBER>

The maximum number of times a test set will be attempted before being
abandoned.  Default is 2.

=back

=head1 TEST-LIST-FILE

The file format is:

  DIRECTORY:EXP-FILE[=SOURCE-PATTERN]

TODO: Expand on this text.

=cut

#========================================================================#

use FindBin;
use lib "$FindBin::Bin/lib";
use Pod::Usage;
use Getopt::Long;
use Cwd qw/abs_path getcwd/;
use File::Temp qw/tempdir/;
use File::Copy;
use IO::Handle;
use IO::Pipe;
use IO::Select;
use boolean;
use POSIX qw/:sys_wait_h :signal_h strftime/;
use Carp::Assert;
use Carp;
use ChildControl;
use Time::HiRes qw/usleep/;
use Net::Ping;

#========================================================================#

# Make croak act like confess.  Good for debugging.
$Carp::Verbose = true;
$| = 1;

#========================================================================#

my $KILL_WAIT_TIME = 10;
my $SIM_STARTUP_TIME = 180;
my $MAX_WAIT_COUNT = 18;

#========================================================================#

my $command_id = 0;
my $ip_counter = 0;
my $original_script_pid = $$;

#========================================================================#

# Argument processing
my $sim_count = 1;
my $sim_log_dir = undef;
my $gcc_build_dir = undef;
my $gcc_src_dir = undef;
my $ezdk_dir = undef;
my $results_dir = undef;
my $test_list_file = undef;
my $max_test_attempts = 2;
my $give_help = false;
GetOptions ("help|h" => \$give_help,
            "sim-count=i" => \$sim_count,
            "sim-log-directory=s" => \$sim_log_dir,
            "gcc-build-directory=s" => \$gcc_build_dir,
            "gcc-src-directory=s" => \$gcc_src_dir,
            "ezdk-directory=s" => \$ezdk_dir,
            "results-directory=s" => \$results_dir,
            "test-list=s" => \$test_list_file,
            "max-test-attempts=i" => \$max_test_attempts,
           );

if ($give_help)
{
  usage ("");
  exit (0);
}

(defined $results_dir) and (-d $results_dir) or
  usage ("The results directory does not exist.");
(defined $gcc_build_dir) and (-d $gcc_build_dir) or
  usage ("The GCC build directory does not exist.");
(defined $ezdk_dir) and (-d $ezdk_dir) or
  usage ("The EZdk directory does not exist.");
(defined $sim_log_dir) and (-d $sim_log_dir) or
  usage ("The simulator log directory does not exist.");
(defined $test_list_file) and (-f $test_list_file) and (-r $test_list_file) or
  usage ("The test list file must be a readable text file.");

#========================================================================#

delete $ENV {EZTESTER_NSIM_TARGET_IP};
exists $ENV {LM_LICENSE_FILE} or
  croak ("Missing LM_LICENSE_FILE environment variable");
exists $ENV {DEJAGNU} or
  croak ("Missing DEJAGNU environment variable");

(system ("arceb-mellanox-linux-uclibc-gcc --version >/dev/null 2>&1") == 0) or
  croak ("Could not  arceb-mellanox-linux-uclibc-gcc in PATH");

#========================================================================#

my $gcc_site_exp_config_file
  = find_gcc_site_exp_config_file ($gcc_build_dir);

# List of test descriptors.  Each entry is a hash reference.
my @test_list = build_test_list ($test_list_file);

#========================================================================#

# A list of all tests that have stopped, but not yet been cleaned up.  This
# is filled in from the SIGCHLD handler.  Each entry will be a hash
# reference with keys '-pid' and '-status'.
my @dead_children = ();

# A list of simulator control processes that have terminated.  This is
# filled in from the SIGCHLD handler.  This is not the simulator itself
# that has crashed, rather the control process.  This is not expected to
# happen.
my @dead_simulators = ();

# Global list of all simulator descriptor hashes.  Each entry is a hash
# reference, and represents a single simulator instance.
my @all_sims = ();

# Hash of SIGCHLD handlers.  The key of each entry is a process id (PID),
# each value is a hash reference for a hash with two keys '-callback' and
# '-data'.  The '-callback' is a function to call, and '-data' is some data
# to pass to the callback function.
#
# The callback function is called with a hash of arguments, the hash keys
# are '-pid', '-status', and '-data'.  The '-pid' is the process id that
# caused the SIGCHLD, the '-status' is the exit status of the process, and
# '-data' is the data argument that was registered in the %sigchld_actions
# hash.
my %sigchld_actions = ();

# Setup the SIGCHLD and SIGINT handlers.
$SIG{CHLD} = \&handle_sigchld;
$SIG {INT} = \&do_exit_cleanup;

#========================================================================#

# Create all of the simulators.
@all_sims = create_all_sims ($sim_count);

#========================================================================#

# This is a hash of all the tests that are currently running.  The key is
# the pid of the process responsible for running the test, the data is a
# hash reference.
my %running_tests = ();

while (true)
{
  # Clean up after any dead child processes.  Do this first, as this might
  # free up a simulator.
  if (scalar (@dead_children) > 0)
  {
    my $child = pop @dead_children;
    cleanup_after_child ($child);
  }

  # None of the simulator control processes should ever die; this is
  # different from the simulator itself dying, that is handled by the
  # simulator control process.  These processes do exit when told to do so
  # at the end of this script, but then we will never reach this code.
  if (scalar (@dead_simulators) > 0)
  {
    my $sim = pop @dead_simulators;
    croak ("Simulator control process for simulator ".
             sim_id ($sim) ." has died unexpectedly.\n");
  }

  # Now try to start any tests that are left to run.
  if (scalar (@test_list) > 0)
  {
    my $sim = find_available_simulator ();

    # Did we find a simulator?
    if (defined $sim)
    {
      # Get the next test to run, and start it running.
      my $test = pop (@test_list);
      start_test ($sim, $test);
    }
  }

  # If we have finished, then exit the main loop.
  if ((scalar (@test_list) == 0)
        and (scalar (@dead_children) == 0)
        and (scalar (keys (%running_tests)) == 0))
  {
    last; # Exit the whle loop.
  }

  # Not finished yet.  Wait for a while and repeat.
  small_delay ();
}

print "[$$] all testing complete.\n";
exit_all_sims ();
exit (0);

#========================================================================#

=pod

=head1 METHODS

The following methods are defined in this script.

=over 4

=cut

#========================================================================#

=pod

=item B<block_signals>

Take a list of signals and arrange for those signals to be blocked.
Return a POSIX::SigSet containing the original signal set.

=cut

sub block_signals {
  my @signals = @_;

  my $sigset = POSIX::SigSet->new (@signals);
  my $old_sigset = POSIX::SigSet->new ();

  sigprocmask(SIG_BLOCK, $sigset, $old_sigset) or
    croak ("Could not block signals in $sigset\n");

  return $old_sigset;
}

#========================================================================#

=pod

=item B<unblock_signals>

Take a list of signals and arrange for those signals to be unblocked.
Return a POSIX::SigSet containing the original signal set.

=cut

sub unblock_signals {
  my @signals = @_;

  my $sigset = POSIX::SigSet->new (@signals);
  my $old_sigset = POSIX::SigSet->new ();

  sigprocmask(SIG_UNBLOCK, $sigset, $old_sigset) or
    croak ("Could not block signals in $sigset\n");

  return $old_sigset;
}

#========================================================================#

=pod

=item B<wait_for_all_child_processes>

Wait for all child processes to exit.  This function should only be
called in the original script process, not in any of the child
processes.

The waiting is done by waiting for the %SIGCHLD_ACTIONS hash to become
empty.  As each SIGCHLD is delivered, the corresponding entry in this
hash is removed, this then is a good indication that all the child
processes have exited.

We only wait for a limited period of time, before issuing a warning,
and returning from this function.

=cut

sub wait_for_all_child_processes {
  assert (in_original_script_process ());

  my $start = time ();
  while ((time () - $start < $KILL_WAIT_TIME)
           and (scalar (keys (%sigchld_actions)) > 0))
  {
    small_delay ();
  }

  if (scalar (keys (%sigchld_actions)) > 0)
  {
    carp ("Child processes ". join (", ", keys (%sigchld_actions))
            ." did not exit");
  }
}

#========================================================================#

=pod

=item B<exit_all_sims>

Send the EXIT command to all active simulators.  This will cause the
simulator to terminate itself.  We then wait for a limited period of
time to give the simulators a chance to exit.

=cut

sub exit_all_sims {
  print "[$$] exiting all active simulators\n";
  foreach my $s (@all_sims)
  {
    if (sim_is_active ($s))
    {
      sim_exit ($s);
    }
  }

  my $start = time ();
  while (time () - $start < $KILL_WAIT_TIME)
  {
    my $active_count = 0;
    foreach my $s (@all_sims)
    {
      if (sim_is_active ($s))
      {
        $active_count++;
      }
    }

    last if ($active_count == 0);
    small_delay ();
  }
  print "[$$] all simulators have exited\n";
}

#========================================================================#

=pod

=item B<do_exit_cleanup>

Perform cleanup before the script exits.  This function is called in the
parent process from a SIGINT handler.

We send the EXIT command to all simulators, which should cause them to
exit, we then wait for all our child processes to exit.  Any running
tests should spot that the simulators have died and terminate
themselves.

In theory this should only ever be called from the original parent
script process, however, we are currently not blocking signals
sufficiently during all of the fork and exec regions, and so,
sometimes, this might be called from a child process.  We just ignore
such calls and return.

=cut

sub do_exit_cleanup {
  return unless (in_original_script_process ());

  print "[$$] exit cleanup\n";

  exit_all_sims ();
  wait_for_all_child_processes ();
}

#========================================================================#

=pod

=item B<read_ip_from_file>

Take a simulator control descriptor hash, and read the 'net.info'
file, which is created within the log directory.  From the 'net.info'
file extract, and return the simulator IP address as a string.

Return undef if the 'net.info' file does not exist, or the IP address
can't be extracted for any reason.

=cut

sub read_ip_from_file {
  my $simulator_status = shift;

  my $log_dir = $simulator_status->{ -log_directory };
  my $filename = $log_dir."/net.info";

  return undef unless (-r $filename);
  open my $in, $filename or return undef;
  my $ip = undef;
  while (<$in>)
  {
    if (m/^interface .* ip (\d+\.\d+\.\d+\.\d+)\s*$/)
    {
      $ip = $1;
      last;
    }
  }
  close $in or return undef;

  return $ip;
}

#========================================================================#

=pod

=item B<in_original_script_process>

Return true if we are in the original script process, othrwise, return
false; this will be when we are in a sub-process of the original
script process.

=cut

sub in_original_script_process {
  return ($$ == $original_script_pid);
}

#========================================================================#

=pod

=item B<usage>

Wrapper around I<pod2usage>.  Takes a message string as a single
parameter, this is passed on to I<pod2usage> along with a specifc set
of parameters to display the help text out of the scripts pod.

=cut

sub usage {
  my $msg = shift;
  pod2usage ({-message => $msg,
              -verbose => 1,
              -exitval => 1});
  exit (1);
}

#========================================================================#

=pod

=item B<do_ping>

Take two parameters, a Net::Ping object, and an ip address, or host
name to ping as a string.  Ping the ip or host, and return true if the
ping is a success, otherwise, return false.

This wrapper blocks SIGCHLD around the call to ping, as the singal can
interrupt the ping, which will cause the ping to appear to fail, when
it really shouldn't.

If the second argument, the IP address, is undefined, then we return
false.

=cut

sub do_ping {
  my $pinger = shift;
  my $ip = shift;

  assert ($pinger->isa ("Net::Ping"));
  return false unless (defined $ip);

  block_signals (SIGCHLD);

  my $result = $pinger->ping ($ip);

  unblock_signals (SIGCHLD);

  return $result;
}

#========================================================================#

=pod

=item B<get_next_ip_address>

Return a string that is the next IP address to use.  Only 256 IP
address will be returned by this routine before it refuses to allocate
any more and just returns an error, these are 172.16.0.2 to
172.16.255.2.

=cut

sub get_next_ip_address {
  assert (in_original_script_process ());
  ($ip_counter < 256) or
    croak ("No more available IP addresses");
  my $ip = sprintf "172.16.%d.2", $ip_counter;
  $ip_counter++;
  return $ip;
}

#========================================================================#

=pod

=item B<sim_send_command>

Take a simulator descriptor hash, and a command string.  Send the
command string to the specified simulator.  Wait for a response, and
return the response.

Return undef if no response is received.

=cut

sub sim_send_command {
  my $sim = shift;
  my $command = shift;

  assert (exists ($sim->{ -write_ctrl_fh }));
  assert (exists ($sim->{ -read_ctrl_fh }));

  my $write = $sim->{ -write_ctrl_fh };
  my $read = $sim->{ -read_ctrl_fh };

  # Ensure we only send one newline at the end.
  chomp ($command);
  print $write $command_id.":".$command."\n";
  my $sent_command_id = $command_id;
  $command_id++;

  # Now we wait for a reply, we only wait upto 10 seconds.
  my $sel = IO::Select->new ($read);
  my $start = time ();
  my $wait_count = 0;
  while ((time () - $start) < 10)
  {
    my @ready = $sel->can_read (1);

    foreach my $fh (@ready)
    {
      assert ($fh == $read);
      my $response = <$fh>;

      # An undefined response indicates the file descriptor was closed,
      # probably the simulator control processes exited for some reason.
      return undef if (not (defined ($response)));

      chomp ($response);

      ($response =~ m/^(\d+):(.*)$/) or
        croak ("Badly formed response '$response'");
      my $response_id = $1;
      $response = uc ($2);

      # Ignore responses that don't match.
      if ($response_id != $sent_command_id)
      {
        print "[$$] response id miss-match\n";
        next;
      }

      return $response if ($response ne "WAIT");

      print "[$$] wait requested by simulator control process\n";
      $start = time ();
      $wait_count++;
      if ($wait_count > $MAX_WAIT_COUNT)
      {
        print "[$$] maxium wait count reached\n";
        $start = 0;
        last;
      }
    }
  }

  # We've given up on getting a response from the simulator control
  # process.  Maybe nothing came at all, or we were asked to wait for
  # too long.
  return undef;
}

#========================================================================#

=pod

=item B<sim_send_reply>

Use from the simulator control process to send a reply back to the
main script process.  Takes simulator descriptor hash, the reply ID
number, and the reply string.

Send the reply string back to the parent process, with the reply id
prefixed on the front.

The reply id will have been extracted from the incoming command
string, the main parent process will only accept replies with the
correct reply id number.

=cut

sub sim_send_reply {
  my $sim = shift;
  my $reply_id = shift;
  my $reply = shift;

  assert (exists ($sim->{ -write_ctrl_fh }));
  my $write = $sim->{ -write_ctrl_fh };

  # Ensure we only send one newline at the end.
  chomp ($reply);
  print $write $reply_id.":".$reply."\n";
}

#========================================================================#

=pod

=item B<sim_restart>

Take a simulator descriptor hash, send the "RESTART" command to the
simulator, and wait for an "OK" reply.

Any other reply will result in an error.

=cut

sub sim_restart {
  my $sim = shift;

  print "[$$] sending RESTART command to simulator ".sim_id ($sim) ."\n";
  my $response = sim_send_command ($sim, "RESTART");
  (defined ($response)) or
    croak ("Got no response to restart request on simulator ".
           sim_id ($sim) ."\n");

  print "[$$] got response '$response' from simulator ". sim_id ($sim) ."\n";
  return if ($response eq "OK"); # Sim is now restarted.
  ($response eq "FAILED") or
    croak ("Unexpected response '$response' to restart ".
           "request on simulator ". sim_id ($sim) ."\n");
  croak ("Failed to restart simulator ". sim_id ($sim) ."\n");
}

#========================================================================#

=pod

=item B<sim_activate>

Take a simulator description hash, and active the simulator.  It is an
error to call this on an already active simulator.

This starts the simulator running, monitors the simulator for crashes, and
also periodically pings the simulator to check if it is still alive.  All
this is achieved by creating a sub-process, and sub-sub-process in which to
run the simulator.  The initial sub-process monitors the sub-sub-process
and replies to status requests about the simulator.

=cut

sub sim_activate {
  my $sim = shift;

  assert (not (sim_is_active ($sim)));
  $sim->{ -active } = true;

  print "[$$] activate simulator ". sim_id ($sim) ."\n";

  # First, create a pipe so that the parent can talk to the simulator
  # control process.
  my $pipe1 = IO::Pipe->new () or
    croak ("Failed to create first pipe: $!");
  my $pipe2 = IO::Pipe->new () or
    croak ("Failed to create second pipe: $!");

  assert (not (exists ($sim->{ -write_ctrl_fh })));
  assert (not (exists ($sim->{ -read_ctrl_fh })));

  my $cc = ChildControl->new ();

  # Don't allow SIGINT or SIGCHLD to arrive during creation of a child
  # process, data structures are still being setup.
  block_signals (SIGINT, SIGCHLD);

  my $pid = fork ();
  (defined $pid) or croak ("Failed to fork: $!");

  if ($pid == 0)
  {
    # Put this child, and all its children into its own process group.
    setpgrp (0, 0) or
      croak ("failed to setpgrp in sim_activate: $!");

    # Extract the filehandles from the IO::Pipe and store them away.  This
    # is how we will communicate with our parent process.
    $pipe1->reader ();
    $pipe2->writer ()->autoflush ();
    $sim->{ -read_ctrl_fh } = $pipe1;
    $sim->{ -write_ctrl_fh } = $pipe2;

    # Restore the default SIGINT behaviour (exit) and clear out the list of
    # child processes.  We are a new generation, and so have no children.
    $SIG {INT} = "DEFAULT";
    %sigchld_actions = ();

    # We can now safely arrange to receive SIGINT and SIGCHLD again.  We'll
    # exit on SIGINT, and when we do create children of our own we will
    # correctly handle their death.
    unblock_signals (SIGINT, SIGCHLD);

    # The parent will tell us when it has finished setting up its data
    # structures.
    $cc->wait_for_parent ();

    # The parent is ready, we can now safely think about starting an actual
    # instance of the simulator.
    run_simulator ($sim);

    croak ("reached unexpected point in sim_activate");
  }

  # Extract the filehandles from the IO::Pipe, turn on autoflush, and store
  # the handles for later use.  These are how we talk to the simulator.
  $pipe1->writer ()->autoflush ();
  $pipe2->reader ();
  $sim->{ -read_ctrl_fh } = $pipe2;
  $sim->{ -write_ctrl_fh } = $pipe1;

  # Record an entry for this child process in the relevant data structure,
  # this will be used when the child dies to ensure we clean up correctly.
  print "[$$] process $pid created to control simulator ".
    sim_id ($sim) ."\n";
  $sigchld_actions {$pid} = { -callback => \&sim_ctrl_sigchld_callback,
                              -data => $sim };

  # We are now ready to handle the death of our child.  Open ourselves up
  # to signals again.
  unblock_signals (SIGINT, SIGCHLD);

  # Finally, let the child continue.
  $cc->start_child ();

  # The simulator control process is now in place.  We have not yet
  # started an actual simulator, this is done by sending a RESTART
  # command to the control process, this is done later.
}

#========================================================================#

=pod

=item B<run_simulator>

Helper function to sim_activate, takes a simulator descriptor hash.  This
function is only ever called in a sub-process of the main script, and so
should never return.

Creates another sub-process that will exec the simulator, then continually
monitor the simulator to check that it is still alive, and responding to
network trafic.  Also monitor the incoming read filehandle that is stored
within the simualtor hash for incoming commands from the main parent
process.  Respond to these commands as appropriate.

Current commands are:

=over 2

=item I<EXIT>

Send an "OK" response, then close down the simulator, and exit.

=item I<STATUS?>

Send either "OK" or "DEAD" response.

=item I<RESTART>

Restart the simulator sub-process.  Kill off the original simulator.

=item I<IP?>

Return the IP addres with witch to attach to this simulator.

=back

=cut

sub run_simulator {
  my $sim = shift;

  assert (not (in_original_script_process ()));

  my $simulator_status = { -alive => false };

  my $pinger = Net::Ping->new ('tcp', 2);
  my $sel = IO::Select->new ($sim->{ -read_ctrl_fh });
  while (true)
  {
    # We either have no simulator running yet, or just a single simulator
    # running.
    assert (scalar (keys (%sigchld_actions)) <= 1);

    # Wait for incoming commands.
    my @ready = $sel->can_read (10);

    foreach my $fh (@ready)
    {
      # For our sanity....
      assert ($fh == $sim->{ -read_ctrl_fh });

      # Process commands.
      my $command = <$fh>;

      if (not (defined ($command)))
      {
        # This indicates that our parent has gone away without asking us to
        # kill ourselves.  Lets just clean up and quit.
        kill_exec_process ($simulator_status);
        croak ("Read control file handle closed unexpectedly, exiting...");
      }

      assert (defined ($command));
      chomp ($command);

      ($command =~ m/^(\d+):(.*)$/) or
        croak ("Badly formed command '$command'");
      my $reply_id = $1;
      $command = uc ($2);

      print "[$$] got command '$command' in simulator ". sim_id ($sim) ."\n";

      if ($command eq "EXIT")
      {
        print "[$$] exiting simulator ". sim_id ($sim) ."\n";
        kill_exec_process ($simulator_status);
        sim_send_reply ($sim, $reply_id, "OK");
        exit (0);
      }
      elsif ($command eq "STATUS?")
      {
        print "[$$] check on status of simulator ". sim_id ($sim) ."\n";

        if ($simulator_status->{ -alive })
        {
          my $simulator_is_gone = false;
          my $ip = read_ip_from_file ($simulator_status);

          if (not (do_ping ($pinger, $ip)))
          {
            if (not ($simulator_status->{ -seen_first_ping }))
            {
              while ($simulator_status->{ -alive }
                       and (time () - $simulator_status->{ -start_time }
                            < $SIM_STARTUP_TIME))
              {
                sim_send_reply ($sim, $reply_id, "WAIT");
                sleep (2);
                if (not (defined ($ip)))
                {
                  $ip = read_ip_from_file ($simulator_status);
                }
                last if (do_ping ($pinger, $ip));
              }
            }

            if (not (do_ping ($pinger, $ip)))
            {
              $simulator_is_gone = true;
            }
          }

          if ((not $simulator_is_gone)
                and $simulator_status->{ -alive })
          {
            assert (defined ($ip));
            $simulator_status->{ -seen_first_ping } = true;
          }

          if ($simulator_is_gone)
          {
            kill_exec_process ($simulator_status);
          }
        }

        if ($simulator_status->{ -alive } )
        {
          print "[$$] simulator is alive\n";
          sim_send_reply ($sim, $reply_id, "OK");
        }
        else
        {
          print "[$$] simulator is dead\n";
          sim_send_reply ($sim, $reply_id, "DEAD");
        }
      }
      elsif ($command eq "RESTART")
      {
        kill_exec_process ($simulator_status);
        exec_simulator_process ($sim, $simulator_status);

        my $ip = read_ip_from_file ($simulator_status);
        if (not (do_ping ($pinger, $ip)))
        {
          if (not ($simulator_status->{ -seen_first_ping }))
          {
            while ($simulator_status->{ -alive }
                     and (time () - $simulator_status->{ -start_time }
                          < $SIM_STARTUP_TIME))
            {
              sim_send_reply ($sim, $reply_id, "WAIT");
              sleep (2);
              if (not (defined ($ip)))
              {
                $ip = read_ip_from_file ($simulator_status);
              }
              last if (do_ping ($pinger, $ip));
            }
          }

          if (not (do_ping ($pinger, $ip)))
          {
            kill_exec_process ($simulator_status);
          }
        }

        if ($simulator_status->{ -alive })
        {
          $simulator_status->{ -seen_first_ping } = true;
          sim_send_reply ($sim, $reply_id, "OK");
        }
        else
        {
          sim_send_reply ($sim, $reply_id, "FAILED");
        }
      }
      elsif ($command eq "IP?")
      {
        my $ip = read_ip_from_file ($simulator_status);
        if (defined ($ip))
        {
          sim_send_reply ($sim, $reply_id, $ip);
        }
        else
        {
          sim_send_reply ($sim, $reply_id, "FAILED");
        }
      }
    }

    # Check to see if the simulator is still alive.  If it is not then we
    # can change the status to mark this instance as dead.
  }

  croak ("reached unexpected point in run_simulator");
}


#========================================================================#

=pod

=item B<exec_simulator_process>

Called in a sub-process of the top level run-tests process, this
function create another child, and in that child, exec's a simulator.

The parameters are a simulator descriptor hash, and a exec-process
descriptor hash for the simulator.

=cut

sub exec_simulator_process {
  my $sim = shift;
  my $simulator_status = shift;

  assert (not (in_original_script_process ()));
  assert (defined ($sim) and (ref ($sim) eq 'HASH'));
  assert (defined ($simulator_status) and (ref ($simulator_status) eq 'HASH'));
  assert (not ($simulator_status->{ -alive }));

  my $log_dir = abs_path ($sim_log_dir."/". sim_id ($sim) .".".
                            strftime ("%Y%m%d%H%M%S", localtime ()));
  mkdir $log_dir or
    croak ("Failed to create '$log_dir': $!");
  mkdir $log_dir."/memory" or
    croak ("Failed to create '${log_dir}/memory': $!");
  mkdir $log_dir."/logs" or
    croak ("Failed to create '${log_dir}/logs': $!");

  # Don't allow SIGINT or SIGCHLD to arrive during creation of a child
  # process, data structures are still being setup.
  block_signals (SIGINT, SIGCHLD);

  my $cc = ChildControl->new ();
  my $pid = fork ();
  (defined $pid) or croak ("Failed to fork: $!");

  if ($pid == 0)
  {
    $cc->wait_for_parent ();

    # Place the simulator into its own process group.
    setpgrp (0, 0) or
      croak ("Unable to set process group: $!");

    # Move into the simulator logging directory.
    chdir ($ezdk_dir) or
      croak ("Failed to chdir '$ezdk_dir': $!");

    # Unblock SIGINT and SIGCHLD before starting the simulator.
    unblock_signals (SIGINT, SIGCHLD);

    my @args = ("${ezdk_dir}/tools/EZsim/bin/EZsim_linux_x86_64",
                "-possible_cpus", "0-4095",
                "-present_cpus", "0-1,16-17",
                "-flash_image", "${ezdk_dir}/ldk/images/sim/flash.img",
                "-net_if_connect", "true",
                "-net_if_create_cmd", "${ezdk_dir}/tools/EZtap/bin/EZtap_linux_x86_64 -ip 172.16.0.0 -mask 255.255.255.0 -log_file ${log_dir}/net.info",
                "-output", "${log_dir}/logs",
                "-memory_out", "${log_dir}/memory",
                "-log_mask", "0x0003");
    print "[$$] exec: ". join (" ", @args). "\n";

    # Last thing before starting the simulator, redirect any stdout
    # and stderr into a file for logging.
    open STDOUT, ">sim.output" or
      croak ("Failed to re-open stdout to file 'sim.output': $!");
    open STDERR, ">&", \*STDOUT or
      croak ("Failed to re-open stderr to stdout: $!");

    { exec @args; };

    croak ("reached unexpected point in simulator");
  }

  # Clear the status array using delete rather than assigning an empty
  # array as the status hash reference was passed in by value, so
  # assigning an empty hash here would simply create a new value for
  # the reference, the original value will still be valid in the
  # caller.
  delete @{$simulator_status}{keys %$simulator_status};

  # Now setup the status hash, and register it with the SIGCHLD action
  # array so we can know if the simulator exits.
  $simulator_status->{ -alive } = true;
  $simulator_status->{ -pid } = $pid;
  $simulator_status->{ -start_time } = time ();
  $simulator_status->{ -seen_first_ping } = false;
  $simulator_status->{ -log_directory } = $log_dir;
  $sigchld_actions {$pid} = { -callback => \&exec_process_sigchld_callback,
                              -data => $simulator_status };
  print "[$$] started process $pid to exec simulator ". sim_id ($sim) ."\n";
  $cc->start_child ();

  # We are now ready to handle the death of our child.  Open ourselves up
  # to signals again.
  unblock_signals (SIGINT, SIGCHLD);

  return $simulator_status;
}

#========================================================================#

=pod

=item B<kill_exec_process>

Take an exec status hash as created in exec_simulator_process or
exec_runtest_process, and try to kill the corresponding exec'd process.

The exec status hash has two keys of interest I<-alive> and I<-pid>.

The SIGCHLD handler is configured to set the I<-alive> field to FALSE when
the process dies thanks to an entry in %sigchld_actions that was added when
the process was created.  In this function we monitor the I<-alive> field
to determine when the process has died.

We use the I<-pid> field to determine the correct process id to kill.

The kill itself is done by first sending a SIGINT, then we wait up to 10
seconds for the process to exit.  If after 10 seconds the process still has
not exited, we send the process a SIGKILL, and again wait for up to 10
seconds for the process to exit.

If for whatever reason the process still has not exited then we remove the
corresponding entry from %sigchld_actions, print a warning, and then just
return.  Not ideal, but will probably never happen.

=cut

sub kill_exec_process {
  my $status = shift;

  # Is this process still around?
  return if (not ($status->{ -alive }));
  assert (not (exists ($status->{ -status })));
  my $pid = $status->{ -pid };

  kill '-INT', $pid or
    croak ("Failed to send SIGINT to simulator pid $pid: $!");

  # The signal can take a while to arrive, we wait for upto 10 seconds
  # before sending a SIGKILL.
  my $start = time ();
  while ((time () - $start) < $KILL_WAIT_TIME)
  {
    usleep (100000); # 0.1 seconds
    return if (not ($status->{ -alive }));
    return if (kill (0, $pid) == 0);
  }

  kill '-KILL', $pid or
    croak ("Failed to send SIGKILL to simulator pid $pid: $!");
  $start = time ();
  while ((time () - $start) < $KILL_WAIT_TIME)
  {
    usleep (100000); # 0.1 seconds
    return if (not ($status->{ -alive }));
    return if (kill (0, $pid) == 0);
  }

  # This process seems to be unkillable.  Just ignore it for now and
  # let it become a zombie, We mark it as dead and fake an exit
  # status.
  if (kill (0, $pid) > 0)
  {
    print "[$$] unable to kill process $pid\n";
  }
  delete $sigchld_actions {$pid} if (exists $sigchld_actions {$pid});
  $status->{ -alive } = false;
  $status->{ -status } = 1;   # Fake, non-zero exit status.
}

#========================================================================#

=pod

=item B<sim_is_active>

Take a string descriptor hash, return TRUE if the simulator is active, that
is has been started, otherwise return FALSE.

There's currently no way to deactivate a simulator, so each simulator
starts deactivated, gets started once, then remains active until the end of
the program run.

=cut

sub sim_is_active {
  my $sim = shift;
  return $sim->{ -active };
}

#========================================================================#

=pod

=item B<sim_id>

Return a string that is the ID for this simulator.  Used to make log
messages identifiable.

=cut

sub sim_id {
  my $sim = shift;
  return $sim->{ -id };
}

#========================================================================#

=pod

=item B<sim_mark_as_unavailable>

Take a simulator description hash, and change its availability flag from
TRUE to FALSE.

It is an error if the simulator is already unavailable.

=cut

sub sim_mark_as_unavailable {
  my $sim = shift;

  assert ($sim->{ -available });
  print "[$$] simulator ". sim_id ($sim) ." is now unavailable.\n";
  $sim->{ -available } = false;
}

#========================================================================#

=pod

=item B<sim_mark_as_available>

Take a simulator description hash, and change its availability flag from
FALSE to TRUE.

It is an error if the simulator is already available.

=cut

sub sim_mark_as_available {
  my $sim = shift;

  assert (not ($sim->{ -available }));
  print "[$$] simulator ". sim_id ($sim) ." is available again.\n";
  $sim->{ -available } = true;
}

#========================================================================#

=pod

=item B<sim_is_available>

Passed a simulator description hash, return TRUE if this simulator is
available for use, that is, no test is already running on this simulator,
otherwise return FALSE.

=cut

sub sim_is_available {
  my $sim = shift;
  return $sim->{ -available };
}

#========================================================================#

=pod

=item B<create_all_sims>

Take a single integer argument, create that many simulators, and
activate them all by calling I<sim_activate>.

Return a list of all the simulator descriptor hashes.

=cut

sub create_all_sims {
  my $count = shift;

  my @sims = ();
  foreach my $i (0...($count - 1))
  {
    my $sim = { -active => false,
                -available => true,
                -id => "SIM_".$i,
              };
    push @sims, $sim;
    sim_activate ($sim);
  }

  return @sims;
}

#========================================================================#

=pod

=item B<sim_exit>

Take a simulator descriptor hash reference, and send the EXIT command to
the simulator.

=cut

sub sim_exit {
  my $sim = shift;

  print "[$$] sending EXIT command to sim ". sim_id ($sim) ."\n";
  my $reply = sim_send_command ($sim, "EXIT");

  # An undefined reply indicates the simulator control process did not
  # respond.  However, in the case of exit we don't really care.
  return if (not (defined ($reply)));

  # Just check that if we did get a reply, it's one we expect.
  assert ($reply eq "OK");
}

#========================================================================#

=pod

=item B<find_available_simulator>

From the global variable I<@all_sims> find a simulator that is
available for running tests, or return undef if there is no available
simulator right now.

An available simulator is one that is not running any tests.  If a
simulator is currently dead, then it is restarted.

=cut

sub find_available_simulator {
  my $found_sim = undef;

  foreach my $sim (@all_sims)
  {
    next if (not (sim_is_available ($sim)));

    # All simulators are activated at creation time.  They can only
    # return to a non-active state if the control process dies.  Maybe
    # we could re-activate the simulator here, however, for now we
    # just assume that the control process never dies, and assert that
    # the simulator is active.
    assert (sim_is_active ($sim));

    if (not (sim_is_alive ($sim)))
    {
      print "[$$] restart simulator ".sim_id ($sim)."\n";
      sim_restart ($sim);
      $found_sim = $sim;
      last;
    }

    $found_sim = $sim;
    last;
  }

  if (defined $found_sim)
  {
    # The sim_is_alive call will block if the simulator is starting
    # up, until the simulator is done.  This will only return FALSE if
    # the simulator fails to start up for some reason.
    if (not (sim_is_alive ($found_sim)))
    {
      print "[$$] sim ". sim_id ($found_sim) ." is not alive\n";
    }

    print "[$$] found simulator ". sim_id ($found_sim)
      ." is available to run tests on.\n";
    sim_mark_as_unavailable ($found_sim);
  }

  return $found_sim;
}

#========================================================================#

=pod

=item B<small_delay>

A small sleep.  Used whenever we're sat in a loop waiting for interesting
things to happen.

=cut

sub small_delay {
  sleep (5);
}

#========================================================================#

=pod

=item B<sim_is_alive>

Take a simulator descriptor hash reference, and return TRUE if the
simulator is currently alive, or FALSE if the simulator is not alive.

A simulator that is not alive might not yet have been activated, the
control process for the simulator might have exited (probably unexpectedly
if you're then calling this), or the simulator itself might be dead.

=cut

sub sim_is_alive {
  my $sim = shift;

  if (not (sim_is_active ($sim)))
  {
    print "[$$] simulator ". sim_id ($sim) ." is not active\n";
    return false;
  }

  print "[$$] sending status request to simulator ". sim_id ($sim) ."\n";
  my $response = sim_send_command ($sim, "STATUS?");
  return false if (not (defined ($response)));

  print "[$$] got response '$response' from simulator ". sim_id ($sim) ."\n";
  return true if ($response eq "OK");
  return false if ($response eq "DEAD");

  croak ("Unknown status '$response' from simulator ". sim_id ($sim) ."\n");
}

#========================================================================#

=pod

=item B<sim_ip>

Take a simulator descriptor hash reference, and return a string that
is the IP address with which to contact this simulator.

=cut

sub sim_ip {
  my $sim = shift;

  my $response = sim_send_command ($sim, "IP?");
  (defined $response) or return undef;

  # Validate and return IP address.
  assert ($response =~ m/^\d+\.\d+\.\d+\.\d+$/);
  return $response;
}

#========================================================================#

=pod

=item B<build_test_list>

Take the name of a file containing a test list, and return an actual
list object containing all of the tests described within the file.

GLOB patterns within the test list file are expanded.

=cut

sub build_test_list {
  my $file = shift;

  my @test_list = ();
  open my $in, $file or
    croak "Failed to open '$file': $!";

  my $glob_directory = $gcc_src_dir."/gcc/testsuite";
  (-d $glob_directory) or
    croak ("Could not find GCC testsuite src directory '$glob_directory'");
  my $cwd = getcwd ();
  chdir $glob_directory or
    croak ("Failed to chdir to '$glob_directory': $!");

  while (my $line = <$in>)
  {
    chomp $line;
    $line =~ s/#.*$//; # Remove comments
    next if ($line =~ m/^\s*$/); # Ignore blank lines.

    ($line =~ m/^([^:]+):(.*)/) or
      croak ("Invalid pattern '$line' in test list at line $.");
    my ($directory, $test_set, $exp_file) = ($1, $2, undef);

    my @source_files = ();
    if ($test_set =~ m/^([^=]+\.exp)$/)
    {
      # Single '.exp' file with no source file specified.
      $exp_file = $1;
      push @source_files, "";
    }
    elsif ($test_set =~ m/^([^=]+\.exp)=(.*)$/)
    {
      # A '.exp' file, along with a source file pattern.
      $exp_file = $1;
      my $glob_pattern = $2;
      @source_files = glob ($glob_pattern);
    }
    else
    {
      croak ("Invalid pattern '$line' in test list at line $.");
    }

    foreach my $file (@source_files)
    {
      my $test = { -directory => $directory,
                   -exp_file => $exp_file,
                   -source_file => $file,
                   -from => { -file => $file, -line => $. },
                   -attempts => 0 };
      push @test_list, $test;
    }
  }

  chdir $cwd or
    croak ("Failed to chdir '$cwd': $!");

  close $in or
    croak "Failed to close '$file': $!";

  return @test_list;
}

#========================================================================#

=pod

=item B<cleanup_after_child>

Take a DEAD_CHILD hash, as created by I<handle_sigchld> and processes it.
This means that the corresponding entry in RUNNING_TESTS is removed, we
check to see if the simulator is still alive, and check the exit value of
the DEAD_CHILD.

If it looks like the child managed to run the tests without the simulator
falling over, then the results are moved to the storage area,

If it looks like the child ran into problem, indicated by either a bad exit
value, or the simulator being down, then we add the tests back into the
queue of tests to run, after incrementing the attempt counter on the test
set.  If the test has been attepted too many times then we abandon this
test.

=cut

sub cleanup_after_child {
  my $dead_child = shift;

  my $pid = $dead_child->{ -pid };
  my $status = $dead_child->{ -status };

  (exists $running_tests {$pid}) or
    croak ("No child with pid $pid known");

  print "[$$] clean up after dead child with pid $pid\n";
  my $child = $running_tests {$pid};
  delete $running_tests {$pid};

  # Did the child exit with a return code of zero?  This is not the return
  # code from runtest itself, but rather our wrapper around runtest.  Our
  # wrapper exits with code 0 even when some of the tests fail.
  my $exit_code = $status >> 8;
  $child->{ -exit_code } = $exit_code;
  print "[$$] exit code for child $pid: $exit_code\n";

  # Is the simulator still running?
  my $sim = $child->{ -sim };
  assert (defined ($sim));
  my $sim_alive = sim_is_alive ($sim);
  print "[$$] simulator used by child with pid $pid is ".
    ($sim_alive ? "Alive" : "Dead") ."\n";

  assert (exists ($child->{ -results_directory }));
  my $result_dir = $child->{ -results_directory };

  if (($child->{ -exit_code } != 0) or (not $sim_alive))
  {
    assert (exists ($child->{ -test }));
    my $test = $child->{ -test };

    assert (exists ($test->{ -attempts }));
    $test->{ -attempts }++;

    if ($test->{ -attempts } < $max_test_attempts)
    {
      print "[$$] adding test set back into list for another attempt\n";
      push @test_list, $test;
    }
    else
    {
      print "[$$] abandoning test set after too many attempts\n";
    }

    open my $out, ">".$result_dir."/INVALID-RESULTS" or
      croak ("Failed to open INVALID-RESULTS file: $!");
    print $out "These tests have failed, results are invalid.\n";
    close $out or
      croak ("Failed to close INVALID-RESULTS file: $!");
  }

  unlink "${result_dir}/INCOMPLETE-RESULTS" or
    croak ("Could not remove ${result_dir}/INCOMPLETE-REMOVE file: $!");

  # The simulator is no longer in use, so mark it as available.
  sim_mark_as_available ($sim);
}

#========================================================================#

=pod

=item B<handle_sigchld>

Called when a child process exits.  Registers that a child has finished,
and adds it to the list of children to be cleaned up.  The actual clean up
is done outside of the signal handler in the main program loop.

=cut

sub handle_sigchld {
  local ($!, $?);

  while ((my $pid = waitpid(-1, WNOHANG)) > 0)
  {
    if (exists ($sigchld_actions {$pid}))
    {
      my $action = $sigchld_actions {$pid};
      delete $sigchld_actions {$pid};

      my $callback = $action->{ -callback };
      my $data = $action->{ -data };

      print "[$$] invoke SIGCHLD callback for process $pid (status $?)\n";
      $callback->( -pid => $pid, -status => $?, -data => $data );
    }
  }
}

#========================================================================#

=pod

=item B<start_test_sigchld_callback>

Callback function that is run when a child of the start_test function
finishes.  This callback takes parameters I<-pid>, I<-status>, and
I<-data>.  The pid is the process ID of the child that exited.  The status
is the exit status of the process, and the data is a reference to an array.

This callback adds a new entry into the array pointed to by data, the new
entry is a hash reference, with keys I<-pid> and I<-status> which are
copies of the data passed into this callback.

=cut

sub start_test_sigchld_callback {
  my %args = @_;

  my $pid = $args { -pid };
  my $status = $args { -status };
  my $data = $args { -data };

  assert (ref ($data) eq 'ARRAY');

  my $dead_child = { -pid => $pid, -status => $? };
  push @{$data}, $dead_child;
}

#========================================================================#

=pod

=item B<exec_process_sigchld_callback>

Callback function that is run when a child of the do_start_test function
finishes.  This callback takes parameters I<-pid>, I<-status>, and
I<-data>.  The pid is the process ID of the child that exited.  The status
is the exit status of the process, and the data is a reference to a hash.

This callback updates the hash passed in the data argument.  The '-alive'
entry of the hash is changed from true to false, and adds a new '-status'
entry to the hash, the value of this new entry is a copy of the status
passed in to this callback function.

=cut

sub exec_process_sigchld_callback {
  my %args = @_;

  my $pid = $args { -pid };
  my $status = $args { -status };
  my $data = $args { -data };

  assert (ref ($data) eq 'HASH');
  assert (exists ($data->{ -alive }));
  assert ($data->{ -alive });
  assert (not (exists ($data->{ -status })));

  $data->{ -alive } = false;
  $data->{ -status } = $?;
}

#========================================================================#

=pod

=item B<sim_ctrl_sigchld_callback>

Callback function that is run when one of the simulator control
processes exits.  This callback takes parameters I<-pid>, I<-status>,
and I<-data>.  The pid is the process ID of the child that exited.
The status is the exit status of the process, and the data is a
reference to a simulator descriptor hash.

Currently we just mark the simulator as non-active, and leave a cookie
that the simulator has died, then we add the simulator to the list of
dead simulators so the main loop can process it.

=cut

sub sim_ctrl_sigchld_callback {
  my %args = @_;

  my $pid = $args { -pid };
  my $status = $args { -status };
  my $data = $args { -data };

  assert (ref ($data) eq 'HASH');

  my $sim = $data;
  assert (exists ($sim->{ -active }));
  assert ($sim->{ -active });

  $sim->{ -active } = false;
  push @dead_simulators, $sim;
}

#========================================================================#

=pod

=item B<start_test>

Takes a SIM descriptor hash, and a TEST descriptor hash.  Start the test
running in a child process.  Add an entry to the RUNNING_TESTS hash to
record that the test is now running.

This function should be called from the main parent process.  This function
will trigger the creation of child processes to handle running the test.

=cut

sub start_test {
  my $sim = shift;
  my $test = shift;

  assert (in_original_script_process ());

  # Within the results directory, create a temporary directory in which to
  # run these tests.
  my $tempdir = abs_path (tempdir ( DIR => $results_dir ));
  print "[$$] created results directory: $tempdir\n";

  open my $out, ">".$tempdir."/INCOMPLETE-RESULTS" or
    croak ("Failed to open INCOMPLETE-RESULTS file: $!");
  print $out "These tests have not completed yet.\n";
  close $out or
    croak ("Failed to close INCOMPLETE-RESULTS file: $!");

  # Create a location within TEMPDIR to hold compiled binaries.
  mkdir "${tempdir}/obj" or
    croak ("Failed to create tmp directory witin ${tempdir}: $!");

  # Copy the site.exp file from the original build tree into the temporary
  # directory.
  open my $site_exp_in, $gcc_site_exp_config_file or
    croak ("Failed to open '$gcc_site_exp_config_file': $!");
  open my $site_exp_out, ">${tempdir}/site.exp" or
    croak ("Failed to open '${tempdir}/site.exp' for writting: $!");
  while (<$site_exp_in>)
  {
    if (m/^set tmpdir /)
    {
      print $site_exp_out "set tmpdir ${tempdir}/obj\n";
    }
    else
    {
      print $site_exp_out $_;
    }
  }
  close $site_exp_out or
    croak ("Failed to close '${tempdir}/site.exp': $!");
  close $site_exp_in or
    croak ("Failed to close '$gcc_site_exp_config_file': $!");

  # Object to control the child process.
  my $cc = ChildControl->new ();

  # Don't allow SIGINT or SIGCHLD to arrive during creation of a child
  # process, data structures are still being setup.
  block_signals (SIGINT, SIGCHLD);

  print "[$$] creating child process to perform tests.\n";
  my $pid = fork ();
  (defined $pid) or
    croak ("fork failed: $!");

  if ($pid == 0)
  {
    # Put this child, and all its children into its own process group.
    setpgrp (0, 0) or
      croak ("failed to setpgrp in start_test: $!");

    # Restore the default SIGINT behaviour (exit) and clear out the list of
    # child processes.  We are a new generation, and so have no children.
    $SIG {INT} = "DEFAULT";
    %sigchld_actions = ();

    # We can now safely arrange to receive SIGINT and SIGCHLD again.  We'll
    # exit on SIGINT, and when we do create children of our own we will
    # correctly handle their death.
    unblock_signals (SIGINT, SIGCHLD);

    # Child, wait for parent to tell us to start, then enter the temporary
    # directory, and start a runtest process.
    $cc->wait_for_parent ();

    # The parent process is ready.  We can now entry the temporary
    # directory we created for running these tests and start them off.
    chdir $tempdir or
      croak ("Failed to enter temporary directory '$tempdir': $!");
    run_test ($sim, $test);

    croak ("unexpected point in child with pid $$");
  }

  # Parent, create a record that the child has been created, and which
  # tests the child is planning to run.
  my $child = { -pid => $pid, -test => $test, -sim => $sim,
                -results_directory => $tempdir };
  $running_tests {$pid} = $child;

  # Now setup the sigchld callback data, so we know what to do when the
  # child terminates.
  $sigchld_actions {$pid} = { -callback => \&start_test_sigchld_callback,
                              -data => \@dead_children };

  # OK, we can now tell the child to continue.  At any point after this the
  # child might exit, but that's OK, we're setup to handle that now.
  print "[$$] child process $pid is ready to start now.\n";
  unblock_signals (SIGINT, SIGCHLD);
  $cc->start_child ();

}

#========================================================================#

=pod

=item B<run_test>

Helper function for start_test.  This is called from a child process
created within start_test.  This function takes care of actually starting
the runtest process, and monitoring the simulator.

This function never returns.  It is only called within a sub-process, and
so it just exits when it has completed it's task, and exit value of 0 if
everything looks OK, otherwise a non-zero exit value to indicate an error.

When this function is called we are already in the temporary directory that
was created to run the tests.

=cut

sub run_test {
  my $sim = shift;
  my $test = shift;

  assert (not (in_original_script_process ()));

  my $runtest_status = { -alive => false };
  exec_runtest_process ($sim, $runtest_status, $test);

  # PARENT: Wait for the child process to finish.  Monitor the simulator to
  # see if it is still active.
  while ($runtest_status->{ -alive } and sim_is_alive ($sim))
  {
    small_delay ();
  }

  if (not (sim_is_alive ($sim)))
  {
    print "[$$] simulator is no longer alive, this test is a failure.\n";

    # Sim appears to have died.
    if ($runtest_status->{ -alive })
    {
      print "[$$] killing runtest process ". $runtest_status->{ -pid } ."\n";
      kill_exec_process ($runtest_status);
    }

    exit (1);
  }

  assert (not ($runtest_status->{ -alive }));

  # Runtest will exit with 0 or 1 depending on whether all the tests
  # passed, or not.  It would be nice to validate if runtest actually
  # produced some results or not, we can do this by looking for a 'gcc.log'
  # and 'gcc.sum' file, then checking that the 'gcc.sum' file has a results
  # total at the end.
  if (not ((-f "gcc.log") and (-f "gcc.sum")))
  {
    print "[$$] could not find gcc.log and/or gcc.sum, ".
      "this test is a failure.\n";
    exit (1);
  }

  open my $in, "gcc.sum" or
    croak ("Failed to open 'gcc.sum': $!");

  my $found_summary_line = false;
  while (<$in>)
  {
    if (m/=== .* Summary ===/)
    {
      $found_summary_line = true;
      last;
    }
  }

  close $in or
    croak ("Failed to close 'gcc.sum': $!");

  if (not $found_summary_line)
  {
    print "[$$] cound not find summary line in gcc.sum file, ".
      "this test is a failure.\n";
    exit (1);
  }

  # Looks like the tests ran, and we got some results.
  print "[$$] test results look promising.\n";
  exit (0);
}

#========================================================================#

=pod

=item B<exec_runtest_process>

This is called for a child process of the original process, and has
the task of creating yet another child process, and then exec-ing,
within that child, the 'runtest' process.

The arguments to this function are the simulator descriptor hash, the
exec-status hash, and the test description hash.

When this function is called the process will already be within the
temporary directory where the results of the runtest should be stored.

=cut

sub exec_runtest_process {
  my $sim = shift;
  my $runtest_status = shift;
  my $test = shift;

  assert (not (in_original_script_process ()));

  my $ip = sim_ip ($sim);
  my $cc = ChildControl->new ();

  # Create a child process.
  print "[$$] creating grandchild process in which to exec runtest\n";
  my $pid = fork ();
  (defined $pid) or
    croak ("fork failed: $!");

  # CHILD: Start the runtest process.
  if ($pid == 0)
  {
    $cc->wait_for_parent ();
    setpgrp (0, 0) or croak ("Unable to set process group: $!");

    $ENV {EZTESTER_NSIM_TARGET_IP} = $ip;

    # In the child, this is where we should become a runtest process...
    my $exp_file = $test->{ -exp_file };
    my $source_file = $test->{ -source_file };
    my $test_spec = $exp_file;
    if ($source_file ne "")
    {
      $test_spec .= "=".$source_file;
    }

    my @args = ("runtest", "--tool", "gcc",
                "--target_board=arc-linux-nsim", $test_spec);

    # Redirect stdout and stderr as the last thing before we exec runtest.
    open STDOUT, ">runtest.output" or
      croak ("Failed to re-open stdout to file 'runtest.output': $!");
    open STDERR, ">&", \*STDOUT or
      croak ("Failed to re-open stderr to stdout: $!");

    # Use braces to suppress warning about 'croak' after 'exec'.
    { exec @args; };

    croak ("[$$] failed to start runtest");
  }

  # Clear the status array using delete rather than assigning an empty
  # array as the status hash reference was passed in by value, so
  # assigning an empty hash here would simply create a new value for
  # the reference, the original value will still be valid in the
  # caller.
  delete @{$runtest_status}{keys %$runtest_status};

  # Now setup the status array to allow us to track whether the
  # runtest process is still alive.
  $runtest_status->{ -alive } = true;
  $runtest_status->{ -pid } = $pid ;
  $sigchld_actions {$pid} = { -callback => \&exec_process_sigchld_callback,
                              -data => $runtest_status };
  print "[$$] grandchild process $pid is ready to go\n";
  $cc->start_child ();

  return $runtest_status;
}

#========================================================================#

=pod

=item B<find_gcc_site_exp_config_file>

Take the path to the GCC build directory.  Rebuild the site.exp file
that is used for testing.  Return a path to this file within the build
tree.

=cut

sub find_gcc_site_exp_config_file {
  my $gcc_build_dir = shift;

  # Rebuild the gcc/site.exp file within the GCC build directory.
  my $cwd = getcwd ();
  chdir $gcc_build_dir or
    croak ("Failed to chdir to '$gcc_build_dir': $!");
  my $command = "make -C gcc/ site.exp";
  (system ($command) == 0) or
    croak ("system '$command' failed: $?");
  my $site_exp_path
    = $gcc_build_dir."/gcc/site.exp";
  (-f $site_exp_path) or
    croak ("Can't find GCC site.exp file: $site_exp_path");
  chdir $cwd or
    croak "Failed to return to '$cwd': $!";
  # Return the path to this file.
  return $site_exp_path;
}

#========================================================================#

=pod

=back

=head1 AUTHOR

Andrew Burgess, 10 Jan 2016

=cut
