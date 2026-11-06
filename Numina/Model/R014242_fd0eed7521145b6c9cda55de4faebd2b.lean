import Mathlib

theorem algebra_114245 (a b c : ℝ) (ha : a < b) (hb : b < c) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 3*x1^2-2*(a+b+c)*x1+a*b+b*c+a*c=0 ∧
      3*x2^2-2*(a+b+c)*x2+a*b+b*c+a*c=0 ∧ a < x1 ∧ x1 < b ∧ b < x2 ∧ x2 < c := by
  have h2 : 0 < b - a := by linarith
  have h3 : 0 < c - b := by linarith
  have h4 : 0 < c - a := by linarith
  have h5 : a^2 + b^2 + c^2 - a*b - b*c - a*c > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith)]
  use (2 * (a + b + c) - Real.sqrt (4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c)) ) / 6, 
    (2 * (a + b + c) + Real.sqrt (4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c)) ) / 6
  constructor
  · -- Show x1 ≠ x2
    by_contra h 
    have h6 : Real.sqrt (4 * (a^2 + b^2 + c^2 - a * b - b * c - a * c)) = 0 := by 
      nlinarith 
    have h7 : 4 * (a^2 + b^2 + c^2 - a * b - b * c - a * c) = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith)] at h6 
      nlinarith 
    have h8 : a^2 + b^2 + c^2 - a * b - b * c - a * c = 0 := by 
      linarith 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), mul_pos (show 0 < b - a by linarith) (show 0 < c - b by linarith)]
  constructor
  · -- Show first root is solution
    nlinarith [Real.sqrt_nonneg (4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c)), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]
  constructor
  · -- Show second root is solution
    nlinarith [Real.sqrt_nonneg (4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c)), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]
  constructor
  · -- Show a < x1
    nlinarith [Real.sqrt_pos.mpr (show 0 < 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]
  constructor
  · -- Show x1 < b
    nlinarith [Real.sqrt_pos.mpr (show 0 < 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]
  constructor
  · -- Show b < x2
    nlinarith [Real.sqrt_pos.mpr (show 0 < 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]
  · -- Show x2 < c
    nlinarith [Real.sqrt_pos.mpr (show 0 < 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - a * c) by nlinarith)]