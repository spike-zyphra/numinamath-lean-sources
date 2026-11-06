import Mathlib

open Real

theorem inequalities_227911 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    6 * a + 4 * b + 5 * c ≥ 5 * sqrt (a * b) + 7 * sqrt (a * c) + 3 * sqrt (b * c) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc

  have h4 : sqrt (a * b) = sqrt a * sqrt b := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h5 : sqrt (a * c) = sqrt a * sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h6 : sqrt (b * c) = sqrt b * sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  rw [h4, h5, h6]

  nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - sqrt c), sq_nonneg (sqrt b - sqrt c), 
    sq_nonneg (sqrt a * sqrt b - sqrt a * sqrt c), sq_nonneg (sqrt a * sqrt b - sqrt b * sqrt c), sq_nonneg (sqrt a * sqrt c - sqrt b * sqrt c),
    Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
    sq_nonneg (sqrt a ^2 - a), sq_nonneg (sqrt b ^2 - b), sq_nonneg (sqrt c ^2 - c),
    Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c), 
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)
  ]