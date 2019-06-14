# Sup

Sup is a process supervisor providing ordered start, stop and cleanup of
a group of processes on POSIX operating systems. Sup puts strong emphasis on
simplicity and reliability, with a goal of as few deviations (zero?) from
the documented behavior as possible in released versions.

Sup is implemented in C with additional help of https://frama-c.com/wp.html.
Wp allows us to write formal proofs regarding different properties in the code provided
our initial assumptions and preconditions are met.
At a minimum this should allow us to eliminate all runtime crashes and undefined behavior in the majority of mission critical code.

# Status

Currently under development, so it does nothing useful yet.