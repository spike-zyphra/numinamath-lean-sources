import Mathlib

open Real

theorem inequalities_104449 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + 2 * y = 1) :
    3 + 2 * sqrt 2 ≤ 1 / x + 1 / y := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 1 / x + 1 / y ≥ 3 + 2 * sqrt 2 := by
    have h3 : 1 / x + 1 / y = (x + y) / (x * y) := by
      field_simp [show 0 < x by linarith, show 0 < y by linarith]
      <;> nlinarith
    rw [h3]
    have h4 : 0 < x * y := h1
    have h5 : (x + y) / (x * y) ≥ 3 + 2 * sqrt 2 := by
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith [sq_nonneg (x - y * Real.sqrt 2), sq_nonneg (y - Real.sqrt 2 / 4), sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (y - 1 / 4), sq_nonneg (x * y - 1 / 8), sq_nonneg (x * Real.sqrt 2 - y * Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), mul_pos hx hy, sq_nonneg (x - 2 * y), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
    linarith
  linarith