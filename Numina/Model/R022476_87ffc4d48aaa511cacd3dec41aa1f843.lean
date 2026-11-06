import Mathlib

theorem algebra_185156 : (2 - Real.sqrt 2 - Real.sqrt 3) / (2 + Real.sqrt 2 - Real.sqrt 3) =
    ((2 * Real.sqrt 6 + 1) * (3 - 4 * Real.sqrt 2)) / 23 := by
  have h1 : 0 < (2 + Real.sqrt 2 - Real.sqrt 3 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
              Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
              sq_nonneg (Real.sqrt 2 - Real.sqrt 3)]
  have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  field_simp [(show 2 + Real.sqrt 2 - Real.sqrt 3 ≠ 0 by linarith [h1]), (show (23 : ℝ) ≠ 0 by norm_num)]
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
                  Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), 
                  sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 3 - 1), 
                  h2, Real.sqrt_nonneg 6]