#include <stddef.h>
#include <stdint.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <poll.h>
#include <errno.h>
#include <signal.h>
#include <string.h>
#include <fcntl.h>
#include <sys/wait.h>
#include "sup.h"

typedef enum {
  SIGNAL_PIPE_EVENT_CHILD,
  SIGNAL_PIPE_EVENT_EXIT,
} SignalPipeEvent;

int signal_pipes[2] = {-1, -1};
sig_atomic_t shutdown_signal_dropped = 0;

static void sig_handler(int signum) {
    int orig_errno = errno;
    char event;
    if (signum == SIGCHLD) {
      event = SIGNAL_PIPE_EVENT_CHILD;
    } else {
      event = SIGNAL_PIPE_EVENT_EXIT;
    }

    while (1) {
      if (write(signal_pipes[1], &event, 1) == -1) {
        if (errno == EINTR)
          continue;
        else if (errno == EAGAIN) {
          if (event == SIGNAL_PIPE_EVENT_EXIT) {
            /* 
              Guarantee that even though the pipe has no room, at least
              one shutdown signal will still be handled again in the future.
            */
            shutdown_signal_dropped = 1;
          }
        } else {
          perror("write failed");
          abort();
        }
      }
      break;
    }
    
    errno = orig_errno;
}

static void make_fd_non_blocking(int fd) {
   int flags;
  while (1) {
    flags = fcntl(fd, F_GETFL, 0);
    if (flags == -1) {
      if (errno == EINTR)
        continue;
      perror("fnctl failed");
      abort();
    }
    break;
  }

  while (1) {
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK | O_CLOEXEC) == -1) {
      if (errno == EINTR)
        continue;
      perror("fnctl failed");
      abort();
    }
    break;
  }
}


void install_signal_handlers(void)
{
  struct sigaction act;
  sigset_t block_mask;
  memset(&act, 0, sizeof(act));
  sigemptyset(&block_mask);
  sigaddset(&block_mask, SIGINT);
  sigaddset(&block_mask, SIGTERM);
  sigaddset(&block_mask, SIGHUP);
  sigaddset(&block_mask, SIGCHLD);
  act.sa_handler = sig_handler;
  act.sa_mask = block_mask;

  while (1) {
    if ((sigaction(SIGTERM, &act, NULL) == -1) ||
        (sigaction(SIGHUP, &act, NULL) == -1)  ||
        (sigaction(SIGINT, &act, NULL) == -1)  ||
        (sigaction(SIGCHLD, &act, NULL) == -1)) {
      if (errno == EINTR)
        continue;
      perror("sigaction failed");
      abort();
    }
    break;
  }

  if (pipe(signal_pipes) == -1)
    abort();

  make_fd_non_blocking(signal_pipes[0]);
  make_fd_non_blocking(signal_pipes[1]);
}

void reset_signal_handlers(void) {
  struct sigaction act;
  sigset_t block_mask;
  memset(&act, 0, sizeof(act));
  sigemptyset(&block_mask);
  act.sa_handler = SIG_DFL;
  act.sa_mask = block_mask;

  while (1) {
    if ((sigaction(SIGTERM, &act, NULL) == -1) ||
        (sigaction(SIGHUP, &act, NULL) == -1)  ||
        (sigaction(SIGINT, &act, NULL) == -1)  ||
        (sigaction(SIGCHLD, &act, NULL) == -1)) {
      if (errno == EINTR)
        continue;
      perror("sigaction failed");
      abort();
    }
    break;
  }
}

static void mask_signals(int how)
{
  sigset_t block_mask;
  sigemptyset(&block_mask);
  sigaddset(&block_mask, SIGINT);
  sigaddset(&block_mask, SIGTERM);
  sigaddset(&block_mask, SIGHUP);
  sigaddset(&block_mask, SIGCHLD);
  
  if (sigprocmask(how, &block_mask, NULL) == -1){
    perror("sigprocmask failed");
    abort();
  }
}

void block_signal_handlers(void)
{
  mask_signals(SIG_BLOCK);
}

void unblock_signal_handlers(void)
{
  mask_signals(SIG_UNBLOCK);
}


WaitResult wait_for_event(int32_t timeout_msecs, pid_t *pid, int *exit)
{
  struct pollfd fds[1];
  int status;
  int pollret;
  uint8_t sig;
  pid_t wpid;

  again:

  if (shutdown_signal_dropped) {
    shutdown_signal_dropped = 0;
    return WAIT_SHUTDOWN_SIGNAL;
  }


#define WAIT_CHILD() do { \
    wpid = waitpid(-1, &status, WNOHANG); \
    if (wpid == -1) { \
      if (errno == EINTR) \
        goto again; \
      perror("waitpid failed"); \
      abort(); \
    } else if (wpid > 0) { \
      *pid = wpid; \
      if WIFSIGNALED(status) { \
        *exit = 129; \
        return WAIT_PROC_DIED; \
      } \
      \
      if WIFEXITED(status) { \
        *exit = WEXITSTATUS(status); \
        return WAIT_PROC_DIED; \
      } \
      \
      goto again;\
    }\
  } while (0)


  // Check once for dead children before blocking.
  // This means if we ever drop a SIGCHLD it will be
  // immediately collected on the next wait_for_event.
  WAIT_CHILD();

  fds[0].fd = signal_pipes[0];
  fds[0].events = POLLIN;

  pollret = poll(fds, 1, timeout_msecs);
  if (pollret == -1) {
    if (errno == EINTR) {
      goto again;
    }
    perror("poll failed");
    abort();
  }

  if (pollret == 0)
    return WAIT_TIMEOUT;

  if (!(fds[0].revents & POLLIN)) {
    abort();
  }

  int nread = read(signal_pipes[0], &sig, 1);

  if (nread == -1) {
    if (errno == EINTR)
      goto again;
    perror("read failed");
    abort();
  }

  if (nread != 1)
    goto again;

  if (sig == SIGNAL_PIPE_EVENT_CHILD) {
    WAIT_CHILD();
    goto again;
  }

  return WAIT_SHUTDOWN_SIGNAL;
}

void unreachable(void)
{
  exit(0);
}

void exec_child(char *prog)
{
  char *const args[2] = {prog, NULL};
  while (1) {
    if (execvp(prog, args) == -1 && errno == EINTR)
      continue;
    perror("execvpe failed");
    abort();
  }
}

void log_event(char *msg)
{
  fprintf(stderr, "%s\n", msg);
}

double restart_tokens_per_second = 0.1;
double restart_token_bucket_capacity = 2.0;
double restart_token_bucket_level = 0.0;

int take_restart_token(void)
{
 
  static int initialized = 0;
  static struct timespec prev_take_time = {0};
  struct timespec t;
  while (1) {
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) {
      if (errno == EINTR)
        continue;
      return 0;
    }
    break;
  }

  if (!initialized) {
    initialized = 1;
    prev_take_time = t;
    restart_token_bucket_level = restart_token_bucket_capacity;
  }

  double elapsed_seconds = (double)(t.tv_sec - prev_take_time.tv_sec)
     + ((double)(t.tv_nsec - prev_take_time.tv_nsec) / 1000000000.0);

  prev_take_time = t;
  restart_token_bucket_level += restart_tokens_per_second * elapsed_seconds;

  if (restart_token_bucket_level > restart_token_bucket_capacity
    || restart_token_bucket_level < 0.0 /* Crazy underflow somehow. */)
    restart_token_bucket_level = restart_token_bucket_capacity;

  if (restart_token_bucket_level < 1.0)
      return 0;

  restart_token_bucket_level -= 1.0;
  return 1;
}
