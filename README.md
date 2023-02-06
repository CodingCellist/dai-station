# Dai Station

Constraint-solver written in Idris2.


# LICENSE

This work is licensed under the BSD-3-Clause license.


# Name?

Constraint-solvers deal with scheduling and rules (amongst other things). As
does the station manager in Ivor the Engine. Welcome to the Idris Cinematic
Universe, I guess ^^


# Evaluation

Some rough performance numbers using `/usr/bin/time` across 3 runs.

## Forward-checking algorithm

| CSP instance | Time w/o initial arc-consist. | Time w. initial arc-consist. |
| ------------ | ----------------------------: | ---------------------------: |
| langfords2_3 |                         0.90s |                        0.87s |
|              |                         0.92s |                        0.88s |
|              |                         0.89s |                        0.93s |
| langfords2_4 |                         0.91s |                        0.95s |
|              |                         0.90s |                        0.91s |
|              |                         0.87s |                        0.87s |
| langfords3_9 |                        53.30s |                       46.29s |
|              |                        53.32s |                       46.43s |
|              |                        54.70s |                       46.46s |

As you can see, there isn't much of a difference until you get to bigger CSP
instances. And even then, the difference is a number of seconds. But hey, it
_is_ faster. (No idea what happened with Langford's 2_4 by the way; an oddity of
the smaller instances maybe?)

