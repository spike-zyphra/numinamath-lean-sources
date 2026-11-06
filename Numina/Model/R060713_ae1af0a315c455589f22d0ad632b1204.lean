import Mathlib

open Real

theorem inequalities_176818 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a + b ≥ sqrt (a * b) + sqrt ((a ^ 2 + b ^ 2) / 2) := by
  have h1 : sqrt (a * b) ≥ 0 := by positivity
  have h2 : sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
  have h3 : (sqrt (a * b)) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    have h4 : 0 ≤ a * b := by nlinarith
    linarith
  have h5 : (sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 = (a ^ 2 + b ^ 2) / 2 := by
    rw [Real.sq_sqrt]
    have h6 : 0 ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
    linarith
  have h7 : (sqrt (a * b) + sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 =
      (sqrt (a * b)) ^ 2 + (sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 + 2 * (sqrt (a * b) * sqrt ((a ^ 2 + b ^ 2) / 2)) := by ring
  have h8 : (a + b) ^ 2 ≥ (sqrt (a * b) + sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 := by
    have h4 : (sqrt (a * b) + sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 =
      (sqrt (a * b)) ^ 2 + (sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 + 2 * (sqrt (a * b) * sqrt ((a ^ 2 + b ^ 2) / 2)) := by ring
    nlinarith [sq_nonneg (a - b), sq_nonneg (sqrt (a * b) - sqrt ((a ^ 2 + b ^ 2) / 2)), 
      h3, h5, Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity),
      mul_pos ha hb, Real.sqrt_nonneg (a * b), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), 
      sq_nonneg (sqrt (a * b) - sqrt ((a ^ 2 + b ^ 2) / 2)), 
      sq_nonneg (a - b)]
  nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), 
    sq_nonneg (a - b), sq_nonneg (sqrt (a * b) - sqrt ((a ^ 2 + b ^ 2) / 2)), 
    h8, h3, h5, Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity)
  ]