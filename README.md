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

## Setup

* Device: Lenovo ThinkPad X1 Extreme (Gen 1)
* CPU: Intel Core i7-8750H (SMT enabled)
* RAM: 1 x 16GB DDR4 @ 2667 MT/s
* OS/Kernel: Arch Linux 6.1.8-hardened1-1-hardened
* Chez-Scheme: v9.5.8
* Idris2: v0.6.0-62811c565

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

## Smallest Domain First (SDF) heuristic

| CSP instance  | Time w/o SDF | Time w. SDF |
| ------------- | -----------: | ----------: |
| langfords3_9  |        47.36 |       44.03 |
|               |        47.61 |       44.07 |
|               |        47.35 |       44.21 |
| langfords3_10 |       305.71 |      238.61 |
|               |       303.91 |      241.25 |
|               |       304.04 |      243.24 |

Once again, the biggest improvements are (predictably, I guess) on the biggest
problem-instances. I have not included the n-queens instances, nor the smaller
Langford's, because the difference is negligible or nonexistent.

See
[the CSV-file](evaln/2023-02-06-sdf-3.csv)
for the complete data.

