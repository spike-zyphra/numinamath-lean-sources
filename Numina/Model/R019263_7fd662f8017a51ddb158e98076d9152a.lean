import Mathlib

open Real

theorem inequalities_207006 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1/3) * (a + b + c)^2 ≥ a * sqrt (b * c) + b * sqrt (c * a) + c * sqrt (a * b) := by
  have h1 : sqrt (b * c) ≤ (b + c) / 2 := by
    nlinarith [Real.sqrt_nonneg (b * c), Real.sq_sqrt (show 0 ≤ b * c by nlinarith), 
      sq_nonneg (b - c)]
  have h2 : sqrt (c * a) ≤ (c + a) / 2 := by
    nlinarith [Real.sqrt_nonneg (c * a), Real.sq_sqrt (show 0 ≤ c * a by nlinarith), 
      sq_nonneg (c - a)]
  have h3 : sqrt (a * b) ≤ (a + b) / 2 := by
    nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith), 
      sq_nonneg (a - b)]
  have h4 : a * sqrt (b * c) ≤ a * ((b + c) / 2) := by
    apply mul_le_mul_of_nonneg_left h1
    linarith
  have h5 : b * sqrt (c * a) ≤ b * ((c + a) / 2) := by
    apply mul_le_mul_of_nonneg_left h2
    linarith
  have h6 : c * sqrt (a * b) ≤ c * ((a + b) / 2) := by
    apply mul_le_mul_of_nonneg_left h3
    linarith
  have h7 : a * ((b + c) / 2) + b * ((c + a) / 2) + c * ((a + b) / 2) = a * b + b * c + c * a := by
    ring
  have h8 : a * sqrt (b * c) + b * sqrt (c * a) + c * sqrt (a * b) ≤ a * b + b * c + c * a := by
    linarith [h4, h5, h6, h7]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]