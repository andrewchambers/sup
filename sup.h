
typedef enum {
    WAIT_TIMEOUT,
    WAIT_PROC_DIED,
    WAIT_SIGTERM,
} WaitResult;

/*@
  assigns *usecs, *pid, *exit;
  ensures \result == WAIT_TIMEOUT 
    || \result == WAIT_PROC_DIED
    || \result == WAIT_SIGTERM;
*/
WaitResult wait(int64_t *usecs, pid_t *pid, int *exit);


/*@
  assigns \nothing;
  ensures \result >= -1;
*/
pid_t spawn(char *prog);


