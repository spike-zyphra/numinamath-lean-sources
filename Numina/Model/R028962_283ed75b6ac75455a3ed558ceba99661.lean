import Mathlib

open Real

theorem inequalities_65690 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * sqrt (3 * a ^ 2 + 6 * b ^ 2) +
    b * sqrt (3 * b ^ 2 + 6 * c ^ 2) +
    c * sqrt (3 * c ^ 2 + 6 * a ^ 2) ≥ (a + b + c) ^ 2 := by
  have h1 : a * sqrt (3 * a ^ 2 + 6 * b ^ 2) ≥ a ^ 2 + 2 * a * b := by
    have h2 : 0 ≤ 3 * a ^ 2 + 6 * b ^ 2 := by nlinarith [sq_nonneg (a), sq_nonneg (b)]
    have h3 : sqrt (3 * a ^ 2 + 6 * b ^ 2) ≥ a + 2 * b := by
      have h4 : (a + 2 * b) ^ 2 ≤ (3 * a ^ 2 + 6 * b ^ 2 : ℝ) := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + 2 * b)]
      have h5 : (a + 2 * b) ≤ sqrt (3 * a ^ 2 + 6 * b ^ 2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    have h6 : a * (sqrt (3 * a ^ 2 + 6 * b ^ 2)) ≥ a * (a + 2 * b) := by
      apply mul_le_mul_of_nonneg_left
      linarith
      all_goals linarith
    have h7 : a * (a + 2 * b) = a ^ 2 + 2 * a * b := by
      ring
    nlinarith [h6, h7]
  have h2 : b * sqrt (3 * b ^ 2 + 6 * c ^ 2) ≥ b ^ 2 + 2 * b * c := by
    have h3 : 0 ≤ 3 * b ^ 2 + 6 * c ^ 2 := by nlinarith [sq_nonneg (b), sq_nonneg (c)]
    have h4 : sqrt (3 * b ^ 2 + 6 * c ^ 2) ≥ b + 2 * c := by
      have h5 : (b + 2 * c) ^ 2 ≤ (3 * b ^ 2 + 6 * c ^ 2 : ℝ) := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (b + 2 * c)]
      have h6 : (b + 2 * c) ≤ sqrt (3 * b ^ 2 + 6 * c ^ 2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    have h7 : b * (sqrt (3 * b ^ 2 + 6 * c ^ 2)) ≥ b * (b + 2 * c) := by
      apply mul_le_mul_of_nonneg_left
      linarith
      all_goals linarith
    have h8 : b * (b + 2 * c) = b ^ 2 + 2 * b * c := by
      ring
    nlinarith [h7, h8]
  have h3 : c * sqrt (3 * c ^ 2 + 6 * a ^ 2) ≥ c ^ 2 + 2 * c * a := by
    have h4 : 0 ≤ 3 * c ^ 2 + 6 * a ^ 2 := by nlinarith [sq_nonneg (c), sq_nonneg (a)]
    have h5 : sqrt (3 * c ^ 2 + 6 * a ^ 2) ≥ c + 2 * a := by
      have h6 : (c + 2 * a) ^ 2 ≤ (3 * c ^ 2 + 6 * a ^ 2 : ℝ) := by
        nlinarith [sq_nonneg (c - a), sq_nonneg (c + 2 * a)]
      have h7 : (c + 2 * a) ≤ sqrt (3 * c ^ 2 + 6 * a ^ 2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    have h8 : c * (sqrt (3 * c ^ 2 + 6 * a ^ 2)) ≥ c * (c + 2 * a) := by
      apply mul_le_mul_of_nonneg_left
      linarith
      all_goals linarith
    have h9 : c * (c + 2 * a) = c ^ 2 + 2 * c * a := by
      ring
    nlinarith [h8, h9]
  nlinarith [h1, h2, h3, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]