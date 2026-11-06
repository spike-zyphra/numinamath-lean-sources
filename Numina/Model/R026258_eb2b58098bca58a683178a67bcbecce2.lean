import Mathlib

theorem algebra_42 {a b : ℝ} (ha : a < 0) (hab : a * b < 0) :
    1 / (|a - b - 3 * √2| - |b - a + √3|) = (3 * √2 + √3) / 15 := by
  have hb : 0 < b := by 
    have h1 : a < 0 := ha
    have h2 : a * b < 0 := hab
    have h3 : b > 0 := by nlinarith
    exact h3
  have h1 : a - b - 3 * Real.sqrt 2 < 0 := by 
    have hb' : 0 < b := hb
    have ha' : a < 0 := ha
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : b - a + Real.sqrt 3 > 0 := by
    have hb' : 0 < b := hb
    have ha' : a < 0 := ha
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h4 : |a - b - 3 * Real.sqrt 2| = -(a - b - 3 * Real.sqrt 2) := by 
    rw [abs_of_neg h1]
  have h5 : |b - a + Real.sqrt 3| = b - a + Real.sqrt 3 := by 
    rw [abs_of_pos h3]
  have h6 : |a - b - 3 * Real.sqrt 2| - |b - a + Real.sqrt 3| = 3 * Real.sqrt 2 - Real.sqrt 3 := by 
    rw [h4, h5]
    ring
  rw [h6]
  have h7 : 1 / (3 * Real.sqrt 2 - Real.sqrt 3) = (3 * Real.sqrt 2 + Real.sqrt 3) / 15 := by 
    have h8 : (3 * Real.sqrt 2 - Real.sqrt 3) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 3)]
    field_simp [h8]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 3), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
  exact h7