
typedef enum {
    WAIT_TIMER_TRIPPED,
    WAIT_PROC_DIED,
    WAIT_TERMINATED,
} WaitResult;

/*@
  assigns \nothing;
  ensures \result == WAIT_TIMER_TRIPPED 
    || \result == WAIT_PROC_DIED;
*/
WaitResult wait(int32_t seconds);


/*@
  assigns \nothing;
*/
int32_t spawn(char *prog);


