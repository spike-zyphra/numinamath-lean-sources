import Mathlib

theorem inequalities_277091 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≥ √(a * b) + √(b * c) + √(a * c) := by
  have h1 : 2 * √(a * b) ≤ a + b := by
    nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb]
  
  have h2 : 2 * √(b * c) ≤ b + c := by
    nlinarith [Real.sqrt_nonneg (b * c), Real.sq_sqrt (show (0 : ℝ) ≤ b * c by positivity), sq_nonneg (b - c), sq_nonneg (b + c), mul_pos hb hc]

  have h3 : 2 * √(a * c) ≤ a + c := by
    nlinarith [Real.sqrt_nonneg (a * c), Real.sq_sqrt (show (0 : ℝ) ≤ a * c by positivity), sq_nonneg (a - c), sq_nonneg (a + c), mul_pos ha hc]

  linarith [h1, h2, h3]