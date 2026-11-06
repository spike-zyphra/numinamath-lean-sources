import Mathlib

theorem algebra_6678 {x : ℝ} (hx : x = Real.sqrt (28 - 16 * Real.sqrt 3)) : x = 4 - 2 * Real.sqrt 3 := by
  have h2 : (4 - 2 * Real.sqrt 3) ^ 2 = 28 - 16 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h3 : Real.sqrt (28 - 16 * Real.sqrt 3) = (4 - 2 * Real.sqrt 3) := by
    have h4 : (4 - 2 * Real.sqrt 3) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h5 : (4 - 2 * Real.sqrt 3) ^ 2 = (28 - 16 * Real.sqrt 3) := h2
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  rw [hx]
  rw [h3]
  all_goals linarith