import Mathlib

theorem inequalities_25526 (a b c : ℝ) (h : a + b + c = 0) :
    0 ≤ (33 * a ^ 2 - a) / (33 * a ^ 2 + 1) + (33 * b ^ 2 - b) / (33 * b ^ 2 + 1) +
        (33 * c ^ 2 - c) / (33 * c ^ 2 + 1) := by 
  have h1 : c = -a - b := by linarith
  rw [h1]
  have h3 : 0 < (33 * a ^ 2 + 1) * (33 * b ^ 2 + 1) * (33 * (-a - b) ^ 2 + 1) := by
    positivity
  have h4 : (33 * a ^ 2 - a) / (33 * a ^ 2 + 1) + (33 * b ^ 2 - b) / (33 * b ^ 2 + 1) +
      (33 * (-a - b) ^ 2 - (-a - b)) / (33 * (-a - b) ^ 2 + 1) ≥ 0 := by
    have h5 : (33 * a ^ 2 - a) / (33 * a ^ 2 + 1) + (33 * b ^ 2 - b) / (33 * b ^ 2 + 1) +
        (33 * (-a - b) ^ 2 - (-a - b)) / (33 * (-a - b) ^ 2 + 1) =
        ( (33 * a ^ 2 - a) * (33 * b ^ 2 + 1) * (33 * (-a - b) ^ 2 + 1) + (33 * b ^ 2 - b) * (33 * a ^ 2 + 1) * (33 * (-a - b) ^ 2 + 1) + (33 * (-a - b) ^ 2 - (-a - b)) * (33 * a ^ 2 + 1) * (33 * b ^ 2 + 1) ) / ((33 * a ^ 2 + 1) * (33 * b ^ 2 + 1) * (33 * (-a - b) ^ 2 + 1)) := by 
      field_simp
      <;> ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - (-a - b)), sq_nonneg (b - (-a - b)), 
      sq_nonneg (a * b), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), 
      sq_nonneg (a + b), sq_nonneg (a - 1/33), sq_nonneg (b - 1/33), sq_nonneg ((-a - b) - 1/33), 
      mul_nonneg (show (0 : ℝ) ≤ 33 * a ^ 2 + 1 by nlinarith) (show (0 : ℝ) ≤ 33 * b ^ 2 + 1 by nlinarith), 
      mul_nonneg (show (0 : ℝ) ≤ 33 * a ^ 2 + 1 by nlinarith) (show (0 : ℝ) ≤ 33 * (-a - b) ^ 2 + 1 by nlinarith), 
      mul_nonneg (show (0 : ℝ) ≤ 33 * b ^ 2 + 1 by nlinarith) (show (0 : ℝ) ≤ 33 * (-a - b) ^ 2 + 1 by nlinarith)]
    all_goals positivity
  linarith