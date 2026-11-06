import Mathlib

open Real

theorem algebra_184136 : sqrt (6.3 * 1.7) * (sqrt (6.3 / 1.7) - sqrt (1.7 / 6.3)) / sqrt ((6.3 + 1.7)^2 - 4 * 6.3 * 1.7) = 1 := by
  have h1 : sqrt (6.3 * 1.7) > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h2 : sqrt ((6.3 + 1.7 : ℝ) ^ 2 - 4 * 6.3 * 1.7) > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h3 : sqrt ((6.3 + 1.7 : ℝ) ^ 2 - 4 * 6.3 * 1.7) = 4.6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : sqrt (6.3 * 1.7 : ℝ) = Real.sqrt (10.71 : ℝ) := by
    norm_num
  have h5 : sqrt (6.3 / 1.7 : ℝ) = Real.sqrt (6.3 : ℝ) / Real.sqrt (1.7 : ℝ) := by
    field_simp [Real.sqrt_div]
  have h6 : sqrt (1.7 / 6.3 : ℝ) = Real.sqrt (1.7 : ℝ) / Real.sqrt (6.3 : ℝ) := by
    field_simp [Real.sqrt_div]
  have eq1 : sqrt (6.3 * 1.7 : ℝ) * (sqrt (6.3 / 1.7 : ℝ) - sqrt (1.7 / 6.3 : ℝ)) = (4.6 : ℝ) := by
    rw [h4]
    have h7 : Real.sqrt (6.3 : ℝ) * Real.sqrt (1.7 : ℝ) = Real.sqrt (10.71 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    have h8 : sqrt (6.3 / 1.7 : ℝ) - sqrt (1.7 / 6.3 : ℝ) = (4.6 / Real.sqrt (10.71 : ℝ)) := by
      rw [h5, h6]
      have h10 : Real.sqrt (6.3 : ℝ) ^ 2 = 6.3 := Real.sq_sqrt (by norm_num)
      have h11 : Real.sqrt (1.7 : ℝ) ^ 2 = 1.7 := Real.sq_sqrt (by norm_num)
      field_simp [h10, h11, h7]
      <;> nlinarith [Real.sqrt_nonneg (6.3 : ℝ), Real.sqrt_nonneg (1.7 : ℝ)]
    rw [h8]
    have h15 : Real.sqrt (10.71 : ℝ) * (4.6 / Real.sqrt (10.71 : ℝ)) = (4.6 : ℝ) := by
      field_simp [show Real.sqrt (10.71 : ℝ) > 0 by positivity]
      <;> nlinarith [Real.sqrt_nonneg (10.71 : ℝ)]
    linarith [h15]
  have eq2 : sqrt (6.3 * 1.7 : ℝ) * (sqrt (6.3 / 1.7 : ℝ) - sqrt (1.7 / 6.3 : ℝ)) / sqrt ((6.3 + 1.7)^2 - 4 * 6.3 * 1.7) = 1 := by
    rw [eq1, h3]
    norm_num
  exact_mod_cast eq2