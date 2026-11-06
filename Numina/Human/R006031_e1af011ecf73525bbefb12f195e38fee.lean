import Mathlib
/-!
## Problem Statement:

A class of 10 students took a math test. Each problem was solved by exactly 7
of the students. If the first nine students each solved 4 problems, how many
problems did the tenth student solve?

## Solution Argument Provided:

Suppose the last student solved $n$ problems, and the total number of problems
on the test was $p$.
Then the total number of correct solutions written can be calculated in two ways:
1. By problems: $p$ problems, each solved by 7 students. Total = $7p$.
2. By students: 9 students solved 4 problems each, and the tenth student solved $n$ problems.
   Total = $9 \times 4 + n = 36 + n$.
Equating these gives $7p = 36 + n$.
This implies $p = (36+n) / 7$, so $36+n$ must be divisible by 7.
Also, the number of problems any student solves cannot exceed the total number
of problems, so $n \leq p$.
Substituting $p$ from the first equation into the inequality:
$n \leq (36+n) / 7$
Assuming $p$ is an integer (which it must be, as it's derived from $7p = 36+n$ where $n \ge 0$), we multiply by 7:
$7n \leq 36 + n$
$6n \leq 36$
$n \leq 6$
We need $n$ such that $n \in \mathbb{N}$, $n \leq 6$, and $7 \mid (36+n)$.
Since $36 \equiv 1 \pmod 7$, we need $7 \mid (1+n)$.
The non-negative integers $n \leq 6$ are $0, 1, 2, 3, 4, 5, 6$.
Testing $n+1$ for divisibility by 7:
- $0+1=1$ (no)
- $1+1=2$ (no)
- $2+1=3$ (no)
- $3+1=4$ (no)
- $4+1=5$ (no)
- $5+1=6$ (no)
- $6+1=7$ (yes)
Thus, the only possibility is $n=6$.

## Formalization in Lean 4:
-/
theorem numbertheory_611213
      -- Let p be the total number of problems (a natural number).
    (p : ℕ)
    -- Let n be the number of problems solved by the 10th student (a natural number).
    (n : ℕ)
    -- Assume the total solutions counted by problems equals total solutions counted by students.
    (h_total_solutions : 7 * p = 9 * 4 + n)
    -- Assume the 10th student's score does not exceed the total number of problems.
    (h_score_bound : n ≤ p)
    -- The theorem asserts that under these conditions, n must be 6.
    : n = 6 := by
    omega
