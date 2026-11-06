import Mathlib

open Real

theorem inequalities_128547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) 
    (hc : 0 < c) (h : a + b + c = 1):
  a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1) ≤
    sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by
  have h1 : 0 ≤ a := by linarith
  have h2 : 0 ≤ b := by linarith
  have h3 : 0 ≤ c := by linarith
  have h2' : a + b + c = 1 := by linarith [h]
  have h7 : 2 - (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h6 : (a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1))^2 ≤ 2 - (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h8 : 0 ≤ (2 * b + 1 : ℝ) := by nlinarith
    have h9 : 0 ≤ (2 * c + 1 : ℝ) := by nlinarith
    have h10 : 0 ≤ (2 * a + 1 : ℝ) := by nlinarith
    have h11 : Real.sqrt (2 * b + 1) ^ 2 = 2 * b + 1 := Real.sq_sqrt (by linarith)
    have h12 : Real.sqrt (2 * c + 1) ^ 2 = 2 * c + 1 := Real.sq_sqrt (by linarith)
    have h13 : Real.sqrt (2 * a + 1) ^ 2 = 2 * a + 1 := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (a * Real.sqrt (2 * c + 1) - b * Real.sqrt (2 * b + 1)), sq_nonneg (b * Real.sqrt (2 * b + 1) - c * Real.sqrt (2 * a + 1)), sq_nonneg (c * Real.sqrt (2 * a + 1) - a * Real.sqrt (2 * b + 1)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, Real.sqrt_nonneg (2 * b + 1), Real.sqrt_nonneg (2 * c + 1), Real.sqrt_nonneg (2 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * b + 1 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * c + 1 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * a + 1 : ℝ) by nlinarith), sq_nonneg (Real.sqrt (2 * b + 1) - Real.sqrt (2 * c + 1)), sq_nonneg (Real.sqrt (2 * c + 1) - Real.sqrt (2 * a + 1)), sq_nonneg (Real.sqrt (2 * a + 1) - Real.sqrt (2 * b + 1))]
  have h8 : a * sqrt (2 * b + 1) + b * sqrt (2 * c + 1) + c * sqrt (2 * a + 1) ≤ Real.sqrt (2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by
    have h9 := Real.le_sqrt_of_sq_le h6
    linarith [Real.sqrt_nonneg (2 - (a ^ 2 + b ^ 2 + c ^ 2))]
  exact h8