

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


/*@
  requires signal_handlers_installed == 0;
  requires signal_handlers_blocked == 0;
  assigns \nothing;
*/
void exec_child(char *prog);


/*@
  assigns \nothing;
*/
void log_event(char *msg);


extern double restart_tokens_per_second;
extern double restart_token_bucket_capacity;
extern double restart_token_bucket_level;

/*@
  assigns restart_token_bucket_level;
*/
int take_restart_token(void);
