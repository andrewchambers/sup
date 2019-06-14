#include <stddef.h>
#include <stdint.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
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
    // The fd is non blocking, on write
    // error we can't do anything but abort

    write_again:
    if (write(signal_pipes[1], &event, 1) == -1) {
      if (errno == EINTR)
        goto write_again;
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
    
    errno = orig_errno;
}

static void make_fd_non_blocking(int fd) {
  int flags = fcntl(fd, F_GETFL, 0);
  if (flags == -1) {
    perror("fnctl failed");
    abort();
  }
  if (fcntl(fd, F_SETFL, flags | O_NONBLOCK | O_CLOEXEC) == -1) {
    perror("fnctl failed");
    abort();
  }
}

void init_signal_handlers(void)
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

  if ((sigaction(SIGTERM, &act, NULL) == -1) ||
      (sigaction(SIGHUP, &act, NULL) == -1)  ||
      (sigaction(SIGINT, &act, NULL) == -1)  ||
      (sigaction(SIGCHLD, &act, NULL) == -1)) {
     perror("sigaction failed");
    abort();
  }

  if (pipe(signal_pipes) == -1)
    abort();

  make_fd_non_blocking(signal_pipes[0]);
  make_fd_non_blocking(signal_pipes[1]);
}

static void reset_signal_handlers(void) {
  struct sigaction act;
  sigset_t block_mask;
  memset(&act, 0, sizeof(act));
  sigemptyset(&block_mask);
  act.sa_handler = SIG_DFL;
  act.sa_mask = block_mask;

  if ((sigaction(SIGTERM, &act, NULL) == -1) ||
      (sigaction(SIGHUP, &act, NULL) == -1)  ||
      (sigaction(SIGINT, &act, NULL) == -1)  ||
      (sigaction(SIGCHLD, &act, NULL) == -1)) {
    perror("sigaction failed");
    abort();
  }
}

static void mask_signals(int how) {
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


pid_t spawn(char *prog)
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


  mask_signals(SIG_BLOCK);

	pid_t pid = fork();

	if (pid > 0) {
    mask_signals(SIG_UNBLOCK);
    setpgid(pid, pid);
		return pid;
	} else if (pid == 0) {
    reset_signal_handlers();
    mask_signals(SIG_UNBLOCK);
    setpgid(pid, pid);
		char *const args[2] = {prog, NULL};
		execvp(prog, args);
		perror("execvpe failed");
		abort();
	} else {
    mask_signals(SIG_UNBLOCK);
    return -1;
  }
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

  if (!fds[0].revents & POLLIN) {
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
  }

  return WAIT_SHUTDOWN_SIGNAL;
}

void unreachable(void)
{
  exit(0);
}