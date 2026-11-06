import Mathlib

theorem algebra_147375 (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (f : ℝ → ℝ)
    (hf : ∀ x, f x = 1 / Real.sqrt (a ^ x)) :
    f (Real.logb a 4) = 1 / 2 := by
  have h1 : f (Real.logb a 4) = 1 / Real.sqrt (a ^ (Real.logb a 4)) := hf (Real.logb a 4)
  have h2 : a ^ (Real.logb a 4) = (4 : ℝ) := by
    have h3 : a ^ (Real.logb a 4) = (4 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals
        try tauto
        try linarith
    linarith
  have h3 : Real.sqrt (a ^ (Real.logb a 4)) = (2 : ℝ) := by
    rw [h2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1, h3]
  all_goals try norm_num