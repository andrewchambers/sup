
typedef enum {
    WAIT_TIMEOUT,
    WAIT_PROC_DIED,
    WAIT_SHUTDOWN_SIGNAL
} WaitResult;

/*@
  assigns *pid, *exit;
  ensures \result == WAIT_TIMEOUT 
    || \result == WAIT_PROC_DIED
    || \result == WAIT_SHUTDOWN_SIGNAL;
*/
WaitResult wait_for_event(int32_t msecs, pid_t *pid, int *exit);


/*@
  assigns \nothing;
  ensures \result >= -1;
*/
pid_t spawn(char *prog);

/*@
  assigns \nothing;
*/
void init_signal_handlers(void);

/*@
  assigns \nothing;
*/
void unreachable(void);
