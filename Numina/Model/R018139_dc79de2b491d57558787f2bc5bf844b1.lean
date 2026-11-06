import Mathlib

theorem algebra_95163 {a x : ℝ} (ha : a ≠ 0) (hx : x ≠ 0) :
    (√(a^2 + x^2) - (x^2 - a^2) / √(a^2 + x^2)) / (a^2 + x^2) =
    2 * a^2 / (a^2 + x^2) ^ ((3 : ℝ) / 2) := by 
  have h1 : (√(a^2 + x^2) - (x^2 - a^2) / √(a^2 + x^2)) = (2 * a^2) / √(a^2 + x^2) := by
    have h2 : √(a^2 + x^2) ≠ 0 := by
      have h3 : a^2 + x^2 > 0 := by
        have h4 : a^2 > 0 := by
          apply sq_pos_of_ne_zero ha
        have h5 : x^2 > 0 := by
          apply sq_pos_of_ne_zero hx
        linarith
      have h6 : √(a^2 + x^2) > 0 := by positivity
      linarith
    field_simp [h2]
    nlinarith [Real.sqrt_nonneg (a^2 + x^2), Real.sq_sqrt (show 0 ≤ a^2 + x^2 by positivity)]
  rw [h1]
  have h3 : a^2 + x^2 > 0 := by
    have h4 : a^2 > 0 := by
      apply sq_pos_of_ne_zero ha
    have h5 : x^2 > 0 := by
      apply sq_pos_of_ne_zero hx
    linarith
  have h4 : (a^2 + x^2 : ℝ) ^ ((3 : ℝ) / 2) = (a^2 + x^2) * √(a^2 + x^2) := by
    have h5 : (a^2 + x^2 : ℝ) ^ ((3 : ℝ) / 2) = (a^2 + x^2 : ℝ) ^ (1 : ℝ) * (a^2 + x^2 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add]
      norm_num
      all_goals positivity
    have h6 : (a^2 + x^2 : ℝ) ^ (1 : ℝ) = (a^2 + x^2 : ℝ) := by
      simp
    have h7 : (a^2 + x^2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (a^2 + x^2) := by
      rw [Real.sqrt_eq_rpow]
    rw [h6, h7] at h5
    linarith
  rw [h4]
  have h7 : √(a^2 + x^2) > 0 := by positivity
  field_simp [Real.sqrt_pos.mpr (show a^2 + x^2 > 0 by positivity), h3]
  all_goals
    nlinarith [Real.sqrt_nonneg (a^2 + x^2), Real.sq_sqrt (show 0 ≤ a^2 + x^2 by positivity)]