import Mathlib

/-Let $k$ be the positive integer 5 and $m$ be the positive integer 3.
Consider the sequence of positive integers $n$ such that $n$ contains at least one digit 0 (in base 10) and $n$ is a multiple of $m$, listed in ascending order. Find the $k$-th number in this sequence. Show the answer is 105.-/

theorem number_theory_638472: 3 ∣ 105 ∧ (105 % 10 = 0 ∨ (105 / 10) % 10 = 0) ∧
    (Finset.filter (fun n => 10 ≤ n ∧ 3 ∣ n ∧ (n % 10 = 0 ∨ (n / 10) % 10 = 0)) (Finset.Icc 1 105)).card = 5 := by

    native_decide