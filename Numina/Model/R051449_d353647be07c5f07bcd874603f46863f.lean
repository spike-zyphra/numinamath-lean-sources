import Mathlib

open Real Set

theorem inequalities_938 (m : ℝ) :
    (∀ x ≥ 1, abs (x + 1) + sqrt (x - 1) ≥ m - abs (x - 2)) ↔ m ≤ 3 := by
  constructor
  · -- Forward implication: if the inequality holds for all $x \geq 1$, then $m \leq 3$
    intro h
    have h1 := h 1 (by norm_num)
    norm_num [abs_of_nonneg, sqrt_eq_iff_sq_eq] at h1 ⊢
    linarith
  · -- Backward implication: if $m \leq 3$, then the inequality holds for all $x \geq 1$
    intro hm x hx
    have h1 : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg]
      linarith
    by_cases h : x < 2
    · -- Case where 1 ≤ x < 2
      have h4 : abs (x - 2) = 2 - x := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      rw [h1, h4]
      have h5 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
      linarith [Real.sqrt_nonneg (x - 1), show (x) - 1 ≥ 0 by linarith, show x - 2 < 0 by linarith]
    · -- Case where x ≥ 2
      have h4 : abs (x - 2) = x - 2 := by
        rw [abs_of_nonneg]
        linarith
        all_goals linarith
      rw [h1, h4]
      have h5 : sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
      linarith [Real.sqrt_nonneg (x - 1), show (x) - 1 ≥ 0 by linarith, show x - 2 ≥ 0 by linarith]