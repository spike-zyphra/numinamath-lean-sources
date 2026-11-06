import Mathlib

theorem inequalities_168215 (a b c d k : ℝ) (h₀ : |k| < 2)
    (h₁ : a^2 + b^2 - k * a * b = 1) (h₂ : c^2 + d^2 - k * c * d = 1) :
    |a * c - b * d| ≤ 2 / Real.sqrt (4 - k^2) := by
  have hk1 : -2 < k := by linarith [abs_lt.mp h₀]
  have hk2 : k < 2 := by linarith [abs_lt.mp h₀]
  have hk3 : 4 - k ^ 2 > 0 := by nlinarith
  have h5 : (a * c - b * d) ^ 2 * (4 - k ^ 2) ≤ 4 := by 
    nlinarith [sq_nonneg (a * d + b * c), sq_nonneg (a * c + b * d), sq_nonneg (a - b - (c - d) * k / 2), sq_nonneg (a + b - (c + d) * k / 2), sq_nonneg (c - d - (a - b) * k / 2), sq_nonneg (c + d - (a + b) * k / 2), sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (k ^ 2 - 2), sq_nonneg ((a * c + b * d) * k - 2 * (a * d + b * c)), sq_nonneg ((a * d + b * c) * k - 2 * (a * c + b * d)), mul_pos (show (0 : ℝ) < 4 - k ^ 2 by nlinarith) (show (0 : ℝ) < 4 - k ^ 2 by nlinarith)]
  have h6 : (a * c - b * d) ^ 2 ≤ 4 / (4 - k^2) := by 
    have hk4 : 4 - k^2 > 0 := by nlinarith
    have hk7 : (a * c - b * d) ^ 2 * (4 - k^2) ≤ 4 := h5
    have hk7' : 0 < 4 - k^2 := by nlinarith
    have h8 : (a * c - b * d) ^ 2 ≤ 4 / (4 - k^2) := by
      apply (le_div_iff₀ (by nlinarith)).mpr 
      nlinarith
    linarith
  have h7 : |a * c - b * d| ≤ Real.sqrt (4 / (4 - k^2)) := by 
    have h8 : (a * c - b * d) ^ 2 ≤ 4 / (4 - k^2) := h6 
    have h9 : |a * c - b * d| = Real.sqrt ((a * c - b * d) ^ 2) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h10 : Real.sqrt ((a * c - b * d) ^ 2) ≤ Real.sqrt (4 / (4 - k^2)) := by 
      apply Real.sqrt_le_sqrt 
      linarith 
    linarith [h9, h10]
  have h8 : Real.sqrt (4 / (4 - k^2)) = 2 / Real.sqrt (4 - k^2) := by
    have hk11 : 4 - k^2 > 0 := by nlinarith
    have h9 : Real.sqrt (4 / (4 - k^2)) = Real.sqrt 4 / Real.sqrt (4 - k^2) := by
      field_simp [Real.sqrt_div]
    have h10 : Real.sqrt (4) = (2 : ℝ) := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h9, h10]
    all_goals positivity
  have h9 : |a * c - b * d| ≤ 2 / Real.sqrt (4 - k^2) := by
    linarith [h7, h8]
  exact h9