/* 
  All code in this file should be proven
  crash free using frama-c wp.
 */


#include <stddef.h>
#include <stdint.h>
#include "sup.h"

#define MAX_PROCS 128

typedef enum {
  	SUPERVISEE_STOPPED,
    SUPERVISEE_CLEANED,
  	SUPERVISEE_STARTING,
  	SUPERVISEE_RUNNING,
  	SUPERVISEE_STOPPING,
} SuperiseeState;


typedef enum {
    OP_OK,
    OP_FAILED,
    OP_CANCELLED,
    OP_LOGIC_BUG,
} OperationResult;

typedef struct {
  SuperiseeState state;
  int64_t pgid;

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

int32_t check_interval_secs = 10;



/*@
  assigns \nothing;
*/
OperationResult run_sync(char *prog, int32_t timeout_secs)
{
  int32_t pid = spawn(prog);
  if (pid == -1)
    return OP_FAILED;

  WaitResult wr = wait(timeout_secs);

  // REAP pid...

  switch (wr) {
  case WAIT_TIMER_TRIPPED:
    return OP_FAILED;
  case WAIT_PROC_DIED:
    return OP_FAILED;
  case WAIT_TERMINATED:
    return OP_CANCELLED;
  }
}


/*@
  assigns supervised[\old(nprocs)];
  assigns nprocs;
*/
int add_supervisee(Supervisee s)
{
	if (nprocs >= MAX_PROCS)
		return 0;
	
	supervised[nprocs] = s;
	nprocs += 1;
	return 1;
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
    return OP_LOGIC_BUG;
  }

  // TODO start clean.

  // TODO wait for clean.
  // or kill clean on other error.

  s->state = SUPERVISEE_CLEANED;
  return OP_OK;
}

/*@
  requires \valid(s);
  assigns \nothing;
*/
OperationResult start_supervisee(Supervisee *s)
{
  if (s->state != SUPERVISEE_CLEANED) {
    return OP_LOGIC_BUG;
  }

  return OP_OK;
}

/*@
  requires \valid(s);
  assigns \nothing;
*/
OperationResult check_supervisee(Supervisee *s)
{
  if (s->state != SUPERVISEE_RUNNING) {
    return OP_LOGIC_BUG;
  }

  return OP_OK;
}

/*@
  requires \valid(s);
  assigns *s;
*/
OperationResult stop_supervisee(Supervisee *s)
{
  s->state = SUPERVISEE_STOPPED;
  return OP_OK;
}

/*@
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
    result = stop_supervisee(&supervised[nprocs-i-1]);
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
  requires 0 <= nprocs <= MAX_PROCS;
  assigns supervised[0 .. nprocs-1];
*/
OperationResult start(void)
{
  /*@
    loop assigns i;
    loop invariant 0 <= i <= nprocs;
  */
  for (int i = 0; i < nprocs; i++) {
    start_supervisee(&supervised[i]);
  }

  return OP_OK;
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
  requires 0 <= nprocs <= MAX_PROCS;
  requires \valid(supervised + (0 .. nprocs-1));
  assigns supervised[0 .. nprocs-1];
*/
OperationResult wait_and_check(void)
{
  WaitResult wr = wait(check_interval_secs);
  if (wr == WAIT_PROC_DIED)
    return OP_FAILED;

  return check();
}


/*@
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

  result = stop();
  if (result != OP_OK)
    ok = 0;
  
  result = clean();
  if (result != OP_OK)
    ok = 0;

  return 1;
}

