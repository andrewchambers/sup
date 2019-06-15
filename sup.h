

/*@ ghost int signal_handlers_installed = 0; */
/*@ ghost int signal_handlers_blocked = 0; */

/*@ predicate signal_handlers_configured{L} = 
  signal_handlers_installed == 1 && signal_handlers_blocked == 0; */

/*@
  ensures signal_handlers_installed == 1;
  assigns signal_handlers_installed;
*/
void install_signal_handlers(void);

/*@
  ensures signal_handlers_installed == 0;
  assigns signal_handlers_installed;
*/
void reset_signal_handlers(void);


/*@
  ensures signal_handlers_blocked == 1;
  assigns signal_handlers_blocked;
*/
void block_signal_handlers(void);

/*@
  ensures signal_handlers_blocked == 0;
  assigns signal_handlers_blocked;
*/
void unblock_signal_handlers(void);


typedef enum {
    WAIT_TIMEOUT,
    WAIT_PROC_DIED,
    WAIT_SHUTDOWN_SIGNAL
} WaitResult;


/*@
  requires signal_handlers_configured;
  assigns *pid, *exit;
  ensures \result == WAIT_TIMEOUT 
    || \result == WAIT_PROC_DIED
    || \result == WAIT_SHUTDOWN_SIGNAL;
*/
WaitResult wait_for_event(int32_t msecs, pid_t *pid, int *exit);


/*@
  assigns \nothing;
*/
void unreachable(void);


