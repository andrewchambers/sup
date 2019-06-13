#include <stddef.h>
#include <stdint.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include "sup.h"

int32_t spawn(char *prog)
{
	pid_t pid = fork();
	if (pid == -1) {
		return -1;
	}

	/*
	  Set a new process group in
	  the parent and the child, one
	  of these should always succeed
	  and we guarantee both ends agree
	  on the process group without a race.

	  I am not sure there is anything
	  useful we can do if both ends error.
	*/
	setpgid(pid, pid);

	if (pid == 0) {
		return pid;
	} else {
		char *const args[2] = {prog, NULL};
		execvp(prog, args);
		perror("execvpe failed");
		exit(1);
	}
}
