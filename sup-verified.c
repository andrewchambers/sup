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

  const char *clean;
  const char *run;
  const char *wait;
  const char *check;
  const char *stop;
} Supervisee;

size_t nprocs = 0;
Supervisee supervised[MAX_PROCS];

double restart_token_bucket_level;
double token_bucket_capacity;

int32_t check_interval_msecs = 10000;

/*@ 
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  ensures \result >= -1;
  ensures signal_handlers_installed == 1;
  ensures signal_handlers_blocked == 0;
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
    // setpgid(pid, pid);
    char *const args[2] = {prog, NULL};
    // execvp(prog, args);
    // perror("execvpe failed");
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
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
void handle_death(pid_t pid, int exitcode)
{
  /*@ 
    loop assigns i, supervised[0 .. nprocs-1];
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs; i++) {
    if (supervised[i].state == SUPERVISEE_RUNNING && supervised[i].pid == pid) {
      supervised[i].state = SUPERVISEE_STOPPED;
      supervised[i].exitcode = exitcode;
    }
  }
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires child > 0;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult wait_for_child(pid_t child, int32_t timeout_msecs)
{
  int termsent = 0;
  int done = 0;
  pid_t dead = 0;
  int exitcode = 0;
  int sigterm = 0;

 /*@ 
    loop assigns done, timeout_msecs, dead, sigterm, termsent;
    loop assigns exitcode, supervised[0 .. nprocs-1];
  */
  while (!done) {
    WaitResult wr = wait_for_event(timeout_msecs, &dead, &exitcode);
    if (wr == WAIT_SHUTDOWN_SIGNAL)
      sigterm = 1;
    
    if (wr == WAIT_SHUTDOWN_SIGNAL || wr == WAIT_TIMEOUT) {
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

  if (sigterm)
    return OP_SHUTDOWN_REQUESTED;

  return exitcode ? OP_FAILED : OP_OK;
}


/*@
  requires 0 <= nprocs < MAX_PROCS;
  assigns nprocs, supervised[\old(nprocs)];
  ensures nprocs == \old(nprocs) + 1;
*/
void add_supervisee(Supervisee s)
{
  supervised[nprocs] = s;
  nprocs = nprocs + 1;
}

/*@
  assigns \nothing;
*/
int take_restart_token(void) {
  return 1;
}

/*@
  requires \valid(s);
  assigns *s;
*/
OperationResult clean_supervisee(Supervisee *s)
{
  if (s->state != SUPERVISEE_STOPPED) {
    unreachable();
    return OP_UNREACHABLE;
  }

  // TODO start clean.

  // TODO wait for clean.
  // or kill clean on other error.

  s->state = SUPERVISEE_CLEANED;
  return OP_OK;
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires 0 <= i <= nprocs-1;
  assigns supervised[i];
  assigns signal_handlers_installed;
  assigns signal_handlers_blocked;
*/
OperationResult start_supervisee(int i)
{
  pid_t pid = -1;
  pid = spawn_child(supervised[i].run);
  //if (pid == -1)
  //  return OP_FAILED;

  supervised[i].state = SUPERVISEE_RUNNING;
  supervised[i].pid = pid;
  return OP_OK;
}

/*@
  requires \valid(s);
  assigns \nothing;
*/
OperationResult check_supervisee(Supervisee *s)
{
  if (s->state != SUPERVISEE_RUNNING) {
    unreachable();
    return OP_UNREACHABLE;
  }

  return OP_OK;
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires 0 <= i <= nprocs-1;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
  ensures supervised[i].state == SUPERVISEE_STOPPED;
*/
OperationResult stop_supervisee(int i)
{
  int gotshutdown = 0;

  if (supervised[i].state == SUPERVISEE_RUNNING) {
    int timeout_msecs = 5000;
    pid_t pid = supervised[i].pid;

    kill(-pid, SIGTERM);
    kill(-pid, SIGCONT);

    /*@ 
      loop assigns gotshutdown, timeout_msecs;
      loop assigns supervised[0 .. nprocs-1];
    */
    while (supervised[i].state == SUPERVISEE_RUNNING) {
      pid_t dead = 0;
      int exitcode = 0;
      
      WaitResult wr = wait_for_event(timeout_msecs, &dead, &exitcode);

      if (wr == WAIT_SHUTDOWN_SIGNAL)
        gotshutdown = 1;
      
      if (wr == WAIT_TIMEOUT) {
        kill(-pid, SIGKILL);
        timeout_msecs = 7000;
      }
      
      if (wr == WAIT_PROC_DIED) {
        handle_death(dead, exitcode);
      }
    }
  }

  supervised[i].state = SUPERVISEE_STOPPED;
  return gotshutdown ? OP_SHUTDOWN_REQUESTED : OP_OK;
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult stop(void)
{
  OperationResult result = OP_OK;

  /*@
    loop assigns i, result, supervised[0..nprocs-1];
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs && result == OP_OK; i++) {
    result = stop_supervisee(nprocs-i-1);
  }

  return result;
}

/*@
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult clean(void)
{
  OperationResult result = OP_OK;

  /*@
    loop assigns i, result, supervised[0..nprocs-1];
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs && result == OP_OK; i++) {
    result = clean_supervisee(&supervised[nprocs-i-1]);
  }

  return result;
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult start(void)
{
  OperationResult result = OP_OK;

  /*@
    loop assigns i, result;
    loop assigns supervised[0 .. nprocs-1];
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs && result == OP_OK; i++) {
    result = start_supervisee(i);
  }

  return result;
}

/*@
  requires \valid(supervised + (0 .. nprocs-1));
  requires 0 <= nprocs <= MAX_PROCS;
  assigns supervised[0 .. nprocs-1];
*/
OperationResult check(void)
{
  /*@
    loop assigns i;
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs; i++) {
    check_supervisee(&supervised[i]);
  }

  return OP_OK;
}

/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult wait_and_check(void)
{

  int done = 0;
  pid_t dead = 0;
  int exitcode = 0;
  int sigterm = 0;

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
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult supervise_once()
{
  OperationResult result;

  result = stop();
  if (result != OP_OK)
    return result;

  result = clean();
  if (result != OP_OK)
    return result;

  result = start();
  if (result != OP_OK)
    return result;

  /*@
  loop invariant \valid(supervised + (0 .. nprocs-1));
  loop assigns supervised[0 .. nprocs-1];
  loop assigns result;
  */
  do {
    result = wait_and_check();
  } while (result == OP_OK);

  return result;
}


/*@
  requires signal_handlers_installed == 1;
  requires signal_handlers_blocked == 0;
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
int supervise_loop(void)
{
  OperationResult result = OP_FAILED;
  int ok = 1;

  /*@
    loop invariant \valid(supervised + (0 .. nprocs-1));
    loop assigns supervised[0 .. nprocs-1];
    loop assigns result;
  */
  while (result == OP_FAILED && take_restart_token()) {
    result = supervise_once();
  }

  if (result != OP_SHUTDOWN_REQUESTED)
    ok = 0;

  result = stop();
  if (result != OP_OK)
    ok = 0;
  
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
    .exitcode = 0,
    .clean = NULL,
    .run = "./foo",
    .wait = NULL,
    .check = NULL,
    .stop = NULL,
  };

  add_supervisee(s);
  supervise_loop();
}
