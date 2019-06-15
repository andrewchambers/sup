/* 
  All code in this file should be proven
  crash free using frama-c wp.
 */


#include <stddef.h>
#include <stdint.h>
#include <unistd.h>
#include <signal.h>

#include "sup.h"

/*
 Define some specifications for external functions we use.
 We must be very careful with our definitions, they
 are close enough for our spec and the properties
 we care about.
*/

/*@
  assigns *status;
 */
pid_t waitpid(pid_t pid, int *status, int options); 

/*@
  assigns \nothing;
 */
int kill(pid_t pid, int sig);

/*@
  assigns \nothing;
*/
int execvp(const char *file, char *const argv[]);

/*@
  requires signal_handlers_blocked == 1;
  assigns \nothing;
  ensures \result >= -1;
*/
pid_t fork(void);

/*@
  assigns \nothing;
*/
int setpgid(pid_t pid, pid_t gpid);


/*@
  assigns \nothing;
*/
void perror(const char *s);

#define MAX_PROCS 128

typedef enum {
  SUPERVISEE_STOPPED,
  SUPERVISEE_CLEANED,
  SUPERVISEE_STARTING,
  SUPERVISEE_RUNNING,
} SuperiseeState;


typedef enum {
  OP_OK,
  OP_FAILED,
  OP_SHUTDOWN_REQUESTED,
  OP_UNREACHABLE,
} OperationResult;

typedef struct {
  SuperiseeState state;
  pid_t pid;
  int exitcode;

  char *clean;
  char *run;
  char *wait;
  char *check;
  char *stop;
} Supervisee;

/*@ predicate valid_supervisee{L}(Supervisee s) = s.pid >= -1; */

size_t nprocs = 0;
Supervisee supervised[MAX_PROCS];

/*@ predicate valid_supervised{L} = 
  (0 <= nprocs <= MAX_PROCS) 
   && (\valid(supervised + (0 .. nprocs-1)))
   && (\forall integer i; 0 <= i < nprocs ==> valid_supervisee(supervised[i])); */
 

int32_t check_interval_msecs = 5000;


/*@ 
  requires signal_handlers_configured;
  ensures \result == -1 || \result > 0;
  ensures signal_handlers_configured;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
*/
pid_t spawn_child(char *prog)
{

  /*
    Mask signals, fork, do some child/parent specific
    setup, and then renable signals.

    We set a new process group in
    the parent and the child, one
    of these should always succeed
    and we guarantee both ends agree
    on the process group without a race.
    I am not sure there is anything
    useful we can do if both ends error, and it 
    cannot be detected.
  */


  block_signal_handlers();

  pid_t pid = fork();

  if (pid > 0) {
    unblock_signal_handlers();
    setpgid(pid, pid);
  } else if (pid == 0) {
    reset_signal_handlers();
    unblock_signal_handlers();
    setpgid(pid, pid);
    exec_child(prog);
    unreachable();
    /*
      This code is unreachable due to exec, but to make
      the post conditions easier we can pretend it keeps running.
    */
    /*@ ghost signal_handlers_installed = 1; */
    pid = -1;
  } else {
    unblock_signal_handlers();
    pid = -1;
  }

  return pid;
}

/*@
  requires valid_supervised;
  ensures valid_supervised;
  assigns supervised[0 .. nprocs-1];
*/
void handle_death(pid_t pid, int exitcode)
{
  /*@ 
    loop assigns i, supervised[0 .. nprocs-1];
    loop invariant 0 <= i <= nprocs;
    loop invariant valid_supervised;
  */
  for (int i = 0; i < nprocs; i++) {
    if (supervised[i].state == SUPERVISEE_RUNNING && supervised[i].pid == pid) {
      supervised[i].state = SUPERVISEE_STOPPED;
      supervised[i].exitcode = exitcode;
    }
  }
}

enum {
  WAIT_FOR_CHILD_FLAG_IGNORE_SHUTDOWN_REQUESTS = 1 << 0,
};

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  requires child > 0;
  assigns supervised[0 .. nprocs-1];
  ensures valid_supervised;
  ensures \result == OP_OK 
    || \result == OP_FAILED 
    || \result == OP_SHUTDOWN_REQUESTED;
*/
OperationResult wait_for_child(pid_t child, int flags, int32_t timeout_msecs)
{
  int termsent = 0;
  int done = 0;
  pid_t dead = 0;
  int exitcode = 0;
  int sigshutdown = 0;

 /*@ 
    loop assigns done, timeout_msecs, dead, sigshutdown, termsent;
    loop assigns exitcode, supervised[0 .. nprocs-1];
    loop invariant valid_supervised;
  */
  while (!done) {
    WaitResult wr = wait_for_event(timeout_msecs, &dead, &exitcode);

    
    if (wr == WAIT_TIMEOUT 
        || (wr == WAIT_SHUTDOWN_SIGNAL && !(flags&WAIT_FOR_CHILD_FLAG_IGNORE_SHUTDOWN_REQUESTS))) {

      if (wr == WAIT_SHUTDOWN_SIGNAL)
        sigshutdown = 1;
      /* 
        Here we send a kill to the pgid.
        What can we do here if kill fails?
        not much, we can progress
        to SIGKILL anyway and try forever
        on 'unkillable' processes.
      */
      kill(-child, termsent == 0 ? SIGTERM : SIGKILL);
      termsent = 1;
      timeout_msecs = 7000;
    }
    
    if (wr == WAIT_PROC_DIED) {
      handle_death(dead, exitcode);
      done = (child == dead);
    }
  }

  if (sigshutdown)
    return OP_SHUTDOWN_REQUESTED;

  if (exitcode != 0)
    return OP_FAILED;

  return OP_OK;
}


/*@
  requires 0 <= nprocs < MAX_PROCS;
  requires valid_supervised;
  requires valid_supervisee(s);
  assigns nprocs, supervised[\old(nprocs)];
  ensures nprocs == \old(nprocs) + 1;
  ensures valid_supervised;
*/
void add_supervisee(Supervisee s)
{
  supervised[nprocs] = s;
  nprocs = nprocs + 1;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  requires 0 <= i < nprocs;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[i];
  ensures signal_handlers_configured;
  ensures valid_supervised;
  ensures supervised[i].state == SUPERVISEE_CLEANED;
  ensures supervised[i].exitcode == -1;
  ensures supervised[i].pid == -1;
*/
OperationResult clean_supervisee(int i)
{
  // TODO start clean.

  // TODO wait for clean.
  // or kill clean on other error.
  supervised[i].state = SUPERVISEE_CLEANED;
  supervised[i].exitcode = -1;
  supervised[i].pid = -1;
  return OP_OK;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  requires 0 <= i < nprocs;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
*/
OperationResult wait_supervisee(int i)
{
 if (!supervised[i].wait)
  return OP_OK;

  pid_t pid = spawn_child(supervised[i].wait);
  if (pid == -1)
    return OP_FAILED;

  return wait_for_child(pid, 0, 5000); /* TODO right timeout */
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  requires 0 <= i < nprocs;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
*/
OperationResult start_supervisee(int i)
{
  pid_t pid = -1;
  pid = spawn_child(supervised[i].run);
  if (pid == -1)
    return OP_FAILED;

  supervised[i].state = SUPERVISEE_RUNNING;
  supervised[i].pid = pid;

  return wait_supervisee(i);
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  requires 0 <= i < nprocs;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
  ensures \result == OP_OK || \result == OP_FAILED || \result == OP_SHUTDOWN_REQUESTED;
*/
OperationResult check_supervisee(int i)
{

  if (supervised[i].check) {
    log_event("checking supervisee.");

    pid_t pid = spawn_child(supervised[i].check);
    if (pid == -1)
      return OP_FAILED;

    OperationResult check_result = wait_for_child(pid, 0, 5000); /* TODO right timeout */
    if (check_result != OP_OK)
      return check_result;
  }

  if (supervised[i].state != SUPERVISEE_RUNNING)
    return OP_FAILED;

  return OP_OK;
}

/*@
  requires signal_handlers_configured;
  requires  valid_supervised;
  requires 0 <= i < nprocs;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
  ensures signal_handlers_configured;
  ensures valid_supervised;
  ensures supervised[i].state == SUPERVISEE_STOPPED;
  ensures \result == OP_OK || \result == OP_SHUTDOWN_REQUESTED;
*/
OperationResult stop_supervisee(int i)
{
  int sigterm_sent = 0;
  int shutdown_requested = 0;
  int timeout_msecs = 5000; /* TODO right timeout */


  if (supervised[i].state == SUPERVISEE_RUNNING) {
    pid_t pid = supervised[i].pid;

    if (supervised[i].stop) {
      log_event("running stop");

      pid_t pid = spawn_child(supervised[i].stop);
      if (pid > 0) {
        OperationResult result = wait_for_child(pid, WAIT_FOR_CHILD_FLAG_IGNORE_SHUTDOWN_REQUESTS, timeout_msecs);
        if (result != OP_OK) {
          log_event("stop command failed, sending SIGTERM");
          kill(-pid, SIGTERM);
          sigterm_sent = 1;
        }
      }
    } else {
       log_event("sending SIGTERM");
       kill(-pid, SIGTERM);
       sigterm_sent = 1;
    }

    /*@ 
      loop invariant valid_supervised;
      loop invariant signal_handlers_configured;
      loop assigns shutdown_requested, timeout_msecs, sigterm_sent;
      loop assigns supervised[0 .. nprocs-1];
    */
    while (supervised[i].state == SUPERVISEE_RUNNING) {
      pid_t dead = 0;
      int exitcode = 0;
      
      WaitResult wr = wait_for_event(timeout_msecs, &dead, &exitcode);

      if (wr == WAIT_SHUTDOWN_SIGNAL)
        shutdown_requested = 1;
      
      if (wr == WAIT_TIMEOUT) {
        log_event("shutdown timeout");
        if (sigterm_sent) {
          log_event("sending SIGKILL");
          kill(-pid, SIGKILL);
        } else {
          log_event("sending SIGTERM");
          kill(-pid, SIGTERM);
        }
        sigterm_sent = 1;
        timeout_msecs = 7000;
      }
      
      if (wr == WAIT_PROC_DIED) {
        handle_death(dead, exitcode);
      }
    }
  }

  supervised[i].state = SUPERVISEE_STOPPED;
  return shutdown_requested ? OP_SHUTDOWN_REQUESTED : OP_OK;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  assigns supervised[0 .. nprocs-1];
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  ensures \result == OP_OK || \result == OP_SHUTDOWN_REQUESTED;
*/
OperationResult stop(void)
{
  int shutdown_requested = 0;
  OperationResult result = OP_OK;

  /*@
    loop assigns i, shutdown_requested, result, supervised[0..nprocs-1];
    loop assigns signal_handlers_installed, signal_handlers_blocked;
    loop invariant signal_handlers_configured;
    loop invariant 0 <= i <= nprocs;
    loop invariant result == OP_OK || result == OP_SHUTDOWN_REQUESTED;
    loop invariant valid_supervised;
  */
  for (int i = 0; i < nprocs ; i++) {
    result = stop_supervisee(nprocs-i-1);
    if (result == OP_SHUTDOWN_REQUESTED)
      shutdown_requested = 1;
  }

  return shutdown_requested ? OP_SHUTDOWN_REQUESTED : OP_OK;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
  ensures valid_supervised;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  ensures \result == OP_OK || \result == OP_SHUTDOWN_REQUESTED || \result == OP_FAILED;
*/
OperationResult clean(void)
{
  int had_error = 0;
  int shutdown_requested = 0;
  OperationResult result = OP_OK;

  /*@
    loop assigns i, result, shutdown_requested, had_error;
    loop assigns signal_handlers_installed;
    loop assigns signal_handlers_blocked;
    loop assigns supervised[0 .. nprocs-1];
    loop invariant valid_supervised;
    loop invariant signal_handlers_configured;
    loop invariant 0 <= i <= nprocs;
    loop variant nprocs - i;
  */
  for (int i = 0; i < nprocs; i++) {
    OperationResult result = clean_supervisee(nprocs-i-1);
    if (result == OP_SHUTDOWN_REQUESTED)
      shutdown_requested = 1;
    if (result == OP_FAILED)
      had_error = 1;
  }

  if (had_error) {
    return OP_FAILED;
  }

  if (shutdown_requested) {
    return OP_SHUTDOWN_REQUESTED;
  }

  return OP_OK;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  assigns supervised[0 .. nprocs-1];
  ensures signal_handlers_configured;
  ensures valid_supervised;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
*/
OperationResult start(void)
{
  OperationResult result = OP_OK;

  /*@
    loop assigns i, result;
    loop assigns signal_handlers_installed;
    loop assigns signal_handlers_blocked;
    loop assigns supervised[0 .. nprocs-1];
    loop invariant valid_supervised;
    loop invariant 0 <= i <= nprocs;
    loop invariant signal_handlers_configured;
    loop variant nprocs - i;
  */
  for (int i = 0; i < nprocs && result == OP_OK; i++) {
    result = start_supervisee(i);
  }

  return result;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  assigns supervised[0 .. nprocs-1];
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  ensures signal_handlers_configured;
  ensures valid_supervised;
  ensures \result == OP_OK || \result == OP_FAILED || \result == OP_SHUTDOWN_REQUESTED;
*/
OperationResult check(void)
{
  OperationResult result = OP_OK;
  /*@
    loop assigns i, result;
    loop assigns signal_handlers_installed;
    loop assigns signal_handlers_blocked;
    loop assigns supervised[0 .. nprocs-1];
    loop invariant valid_supervised;
    loop invariant 0 <= i <= nprocs;
    loop invariant signal_handlers_configured;
    loop invariant result == OP_OK || result == OP_FAILED || result == OP_SHUTDOWN_REQUESTED;
    loop variant nprocs - i;
  */
  for (int i = 0; i < nprocs && result == OP_OK; i++) {
    result = check_supervisee(i);
  }

  return result;
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  assigns supervised[0 .. nprocs-1];
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  ensures signal_handlers_configured;
  ensures valid_supervised;
*/
OperationResult wait_and_check(void)
{

  int done = 0;
  pid_t dead = 0;
  int exitcode = 0;

  WaitResult wr = wait_for_event(check_interval_msecs, &dead, &exitcode);
  if (wr == WAIT_SHUTDOWN_SIGNAL) {
    return OP_SHUTDOWN_REQUESTED;
  } else if (wr == WAIT_PROC_DIED) {
    handle_death(dead, exitcode);
    return OP_FAILED;
  } else if (wr == WAIT_TIMEOUT) {
    return check();
  } else {
    unreachable();
    return OP_UNREACHABLE;
  }
}

/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  ensures valid_supervised;
  ensures signal_handlers_configured;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns supervised[0 .. nprocs-1];
*/
OperationResult supervise_once()
{
  OperationResult result;


  log_event("stopping children");
  result = stop();
  if (result != OP_OK)
    return result;

  log_event("cleaning up after children");
  result = clean();
  if (result != OP_OK)
    return result;

  log_event("starting children");
  result = start();
  if (result != OP_OK)
    return result;

  log_event("starting child supervision");
  /*@
  loop invariant valid_supervised;
  loop invariant signal_handlers_configured;
  loop assigns signal_handlers_installed, signal_handlers_blocked;
  loop assigns result, supervised[0 .. nprocs-1];
  */
  do {
    result = wait_and_check();
  } while (result == OP_OK);

  return result;
}


/*@
  requires signal_handlers_configured;
  requires valid_supervised;
  ensures signal_handlers_configured;
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
  assigns restart_token_bucket_level;
  assigns supervised[0 .. nprocs-1];
*/
int supervise_loop(void)
{
  OperationResult result = OP_OK;
  int ok = 1;
  int has_restart_token = 0;

  /*@
    loop invariant valid_supervised;
    loop invariant signal_handlers_configured;
    loop assigns supervised[0 .. nprocs-1];
    loop assigns result;
    loop assigns has_restart_token;
    loop assigns restart_token_bucket_level;
    loop assigns signal_handlers_installed, signal_handlers_blocked;
  */
  do {
    log_event("supervisor (re)starting chilren");
    result = supervise_once();
    has_restart_token = take_restart_token();
  } while (result == OP_FAILED && has_restart_token);

  if (result == OP_SHUTDOWN_REQUESTED) {
    log_event("got a shutdown request");
  } else if (!has_restart_token) {
    log_event("exhausted restart tokens");
  }

  if (result != OP_SHUTDOWN_REQUESTED)
    ok = 0;

  log_event("performing shutdown, stopping children");
  result = stop();
  /*@ assert result == OP_OK || result == OP_SHUTDOWN_REQUESTED; */

  /*@ 
    loop assigns i, ok;
    loop invariant 0 <= i <= nprocs;
    loop invariant signal_handlers_configured;
  */
  for (int i = 0; i < nprocs; i++) {
    /*
      If the exit code was set, and it wasn't zero we had an error.
    */
    if (supervised[i].exitcode > 0) {
      log_event("shutdown was not clean");
      ok = 0;
    }
  }
  
  log_event("performing shutdown, cleaning up");
  result = clean();
  if (result != OP_OK)
    ok = 0;

  return ok;
}

/*@
  requires signal_handlers_installed == 0;
  requires signal_handlers_blocked == 0;
  requires nprocs == 0;
*/
int main (int argc, char **argv)
{
  install_signal_handlers();
  
  Supervisee s = (Supervisee) {
    .state = SUPERVISEE_STOPPED,
    .pid = -1,
    .exitcode = -1,
    .clean = NULL,
    .run = "./run",
    .wait = "./wait",
    .check = "./check",
    .stop = "./stop",
  };

  add_supervisee(s);
  return supervise_loop() ? 0 : 1;
}
