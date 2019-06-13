# Sup

Sup is a process supervisor providing ordered start, stop and cleanup of
a group of processes on POSIX operating systems. Sup puts strong emphasis on
simplicity and reliability, with a goal of as few deviations (zero?) from
the documented behavior (bugs) as possible in released versions.

Sup is implemented in C with additional help of https://frama-c.com/wp.html. Wp
allows us to write formal proofs regarding different properties in the code.
At a minimum it allows us to eliminate all runtime crashes providing memory safety.

