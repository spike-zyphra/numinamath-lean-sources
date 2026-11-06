import Mathlib

theorem algebra_20846 (a b c d : ℝ) (ha : (4 : ℝ) ^ a = 5) (hb : (5 : ℝ) ^ b = 6)
    (hc : (6 : ℝ) ^ c = 7) (hd : (7 : ℝ) ^ d = 8) :
    a * b * c * d = 3 / 2 := by
  have ha2 : a = Real.logb 4 5 := by
    rw [← ha]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hb2 : b = Real.logb 5 6 := by
    rw [← hb]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hc2 : c = Real.logb 6 7 := by
    rw [← hc]
    field_simp [Real.logb_eq_iff_rpow_eq]
  have hd2 : d = Real.logb 7 8 := by
    rw [← hd]
    field_simp [Real.logb_eq_iff_rpow_eq]
  rw [ha2, hb2, hc2, hd2]
  have h1 : Real.logb 4 5 * Real.logb 5 6 = Real.logb 4 6 := by
    field_simp [Real.logb]
    <;> ring
  have h2 : Real.logb 4 6 * Real.logb 6 7 = Real.logb 4 7 := by
    field_simp [Real.logb]
    <;> ring
  have h3 : Real.logb 4 7 * Real.logb 7 8 = Real.logb 4 8 := by
    field_simp [Real.logb]
    <;> ring
  have h4 : Real.logb 4 8 = 3 / 2 := by
    rw [Real.logb]
    have h5 : Real.log 8 = 3 * Real.log 2 := by
      have h1 : (8 : ℝ) = 2 ^ 3 := by norm_num
      rw [h1]
      simp [Real.log_pow]
      all_goals linarith
    have h6 : Real.log 4 = 2 * Real.log 2 := by
      have h1 : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h1]
      simp [Real.log_pow]
      all_goals linarith
    rw [h5, h6]
    have h7 : Real.log 2 ≠ 0 := by
      positivity
    field_simp [h7]
    <;> ring
  calc
    Real.logb 4 5 * Real.logb 5 6 * Real.logb 6 7 * Real.logb 7 8
        = (Real.logb 4 5 * Real.logb 5 6) * (Real.logb 6 7 * Real.logb 7 8) := by ring
    _ = Real.logb 4 6 * (Real.logb 6 7 * Real.logb 7 8) := by rw [h1]
    _ = (Real.logb 4 6 * Real.logb 6 7) * Real.logb 7 8 := by ring
    _ = Real.logb 4 7 * Real.logb 7 8 := by rw [h2]
    _ = Real.logb 4 8 := by rw [h3]
    _ = 3 / 2 := by rw [h4]