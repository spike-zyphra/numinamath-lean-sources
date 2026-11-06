import Mathlib

open Real

theorem inequalities_254070 (x : ℝ) :
    (0.1 : ℝ) ^ (4 * x ^ 2 - 2 * x - 2) ≤ (0.1 : ℝ) ^ (2 * x - 3) ↔
    (2 * x - 1) ^ 2 ≥ 0 := by
  constructor
  · -- Assume $(0.1)^{4x^2-2x-2} \leq (0.1)^{2x-3}$, we need to prove $(2x-1)^2 \geq 0$
    intro h
    have h1 : 4 * x ^ 2 - 2 * x - 2 ≥ 2 * x - 3 := by
      by_contra h2
      push_neg at h2
      have h2' : (0.1 : ℝ) ^ (4 * x ^ 2 - 2 * x - 2) > (0.1 : ℝ) ^ (2 * x - 3) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals
          norm_num
        all_goals
          nlinarith
      linarith
    have h2 : (2 * x - 1) ^ 2 ≥ 0 := by
      nlinarith [h1]
    exact h2
  · -- Assume $(2x-1)^2 \geq 0$, prove $(0.1)^{4x^2-2x-2} \leq (0.1)^{2x-3}$
    intro h
    have h1 : 4 * x ^ 2 - 2 * x - 2 ≥ 2 * x - 3 := by
      nlinarith [sq_nonneg (2 * x - 1)]
    have h2 : (0.1 : ℝ) ^ (4 * x ^ 2 - 2 * x - 2) ≤ (0.1 : ℝ) ^ (2 * x - 3) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      all_goals
        norm_num
      all_goals
        nlinarith
    exact h2