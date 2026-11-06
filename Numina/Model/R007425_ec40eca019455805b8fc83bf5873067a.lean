import Mathlib
open Real

theorem algebra_93094 : Real.sqrt (4 / 3) - Real.sqrt (3 / 4) = Real.sqrt 3 / 6 := by
  have h1 : Real.sqrt (4 / 3) = 2 / Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [h1, h2]
  have h3 : Real.sqrt 3 > 0 := by positivity
  field_simp [h3]
  <;> ring_nf <;> norm_num
  all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]