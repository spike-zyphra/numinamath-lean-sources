import Mathlib

theorem inequalities_88752 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a^4 + b^4 + c^4 + d^4 + 2*a*b*c*d ≥ a^2*b^2 + a^2*c^2 + a^2*d^2 + b^2*c^2 + b^2*d^2 + c^2*d^2 := by
  have h1 : 0 ≤ a * b * c * d := by
    positivity
  have h2 : a^4 + b^4 ≥ 2 * a^2 * b^2 := by
    nlinarith [sq_nonneg (a^2 - b^2)]
  have h3 : a^4 + c^4 ≥ 2 * a^2 * c^2 := by
    nlinarith [sq_nonneg (a^2 - c^2)]
  have h4 : a^4 + d^4 ≥ 2 * a^2 * d^2 := by
    nlinarith [sq_nonneg (a^2 - d^2)]
  have h5 : b^4 + c^4 ≥ 2 * b^2 * c^2 := by
    nlinarith [sq_nonneg (b^2 - c^2)]
  have h6 : b^4 + d^4 ≥ 2 * b^2 * d^2 := by
    nlinarith [sq_nonneg (b^2 - d^2)]
  have h7 : c^4 + d^4 ≥ 2 * c^2 * d^2 := by
    nlinarith [sq_nonneg (c^2 - d^2)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
    sq_nonneg (a * b - c * d), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), 
    mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, 
    mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd, 
    mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by positivity) (show (0 : ℝ) ≤ b ^ 2 by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by positivity) (show (0 : ℝ) ≤ c ^ 2 by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ a ^ 2 by positivity) (show (0 : ℝ) ≤ d ^ 2 by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ b ^ 2 by positivity) (show (0 : ℝ) ≤ c ^ 2 by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ b ^ 2 by positivity) (show (0 : ℝ) ≤ d ^ 2 by positivity), 
    mul_nonneg (show (0 : ℝ) ≤ c ^ 2 by positivity) (show (0 : ℝ) ≤ d ^ 2 by positivity)
  ]