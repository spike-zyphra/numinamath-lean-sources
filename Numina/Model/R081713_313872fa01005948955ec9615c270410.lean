import Mathlib

open Real Set
open scoped BigOperators

/- Let $a$, $b$ be real numbers, and the function $f(x) = ax + b$ satisfies: for any $x \in \left[ 0,1 \right]$, $\left| f(x) \right| \leqslant 1$. Then the maximum value of $ab$ is ___          ___. -/
theorem algebra_12152 (a b : ℝ) (h : ∀ x ∈ Icc 0 1, |a * x + b| ≤ 1) :
    a * b ≤ 1 / 4 := by 
  have h1 := h 0 (left_mem_Icc.mpr (by norm_num))
  have h2 := h 1 (right_mem_Icc.mpr (by norm_num))
  have h3 := h (1 / 2) (by norm_num [mem_Icc])
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - 1 / 2), sq_nonneg (b + 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2)]