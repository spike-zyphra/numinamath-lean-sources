import Mathlib

theorem algebra_311401 {x : ℝ} (hx : x = 1 / (2 - Real.sqrt 5)) : x^3 + 3 * x^2 - 5 * x + 1 = 0 := by
  have h1 : x = -2 - Real.sqrt 5 := by
    rw [hx]
    have h2 : 2 - Real.sqrt 5 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    field_simp [h2]
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  have h2 : x^2 + 4 * x - 1 = 0 := by
    rw [h1]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  have h3 : x^3 + 3 * x^2 - 5 * x + 1 = (x^2 + 4 * x - 1) * (x - 1) := by
    ring
  rw [h3, h2]
  simp