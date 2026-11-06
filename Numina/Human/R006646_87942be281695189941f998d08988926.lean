import Mathlib

/- Let $P_0$ be an arbitrary prime number strictly greater than 2.
Determine the prime number $p$ such that $\frac{1}{P_0+1} < \frac{1}{p} < \frac{1}{P_0-1}$.
Show the answer is $p=P_0$.-/

theorem number_theory_639639 (P_0 p: ℤ) (h0: 0 < p) (h1: 2 < P_0) (h2: (1: ℚ) / (P_0 + 1) < (1: ℚ) / p) (h3: (1: ℚ) / p < (1: ℚ) / (P_0 - 1)) :
  p = P_0 := by

  apply lt_of_one_div_lt_one_div at h2
  apply lt_of_one_div_lt_one_div at h3
  norm_cast at h2 h3
  omega
  all_goals
    qify at *
    linarith