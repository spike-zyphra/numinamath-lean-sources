import Mathlib

open Real

theorem inequalities_597537 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
  have h1 : 0 ≤ (sqrt a - 1) ^ 2 := by nlinarith
  have h2 : 0 ≤ (sqrt b - 1) ^ 2 := by nlinarith
  have h3 : 0 ≤ (sqrt c - 1) ^ 2 := by nlinarith
  have h4 : (sqrt a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h5 : (sqrt b) ^ 2 = b := by
    rw [Real.sq_sqrt]
    linarith
  have h6 : (sqrt c) ^ 2 = c := by
    rw [Real.sq_sqrt]
    linarith
  have h7 : sqrt a ≥ 0 := by positivity
  have h8 : sqrt b ≥ 0 := by positivity
  have h9 : sqrt c ≥ 0 := by positivity
  nlinarith [sq_nonneg (sqrt a - 1), sq_nonneg (sqrt b - 1), sq_nonneg (sqrt c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
          mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c)
          ]