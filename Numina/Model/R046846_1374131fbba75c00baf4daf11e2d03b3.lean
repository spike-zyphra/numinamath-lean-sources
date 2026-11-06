import Mathlib

open Real

theorem inequalities_312684 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    sqrt (a + (1 / 4) * (b - c) ^ 2) +
    sqrt (b + (1 / 4) * (c - a) ^ 2) +
    sqrt (c + (1 / 4) * (a - b) ^ 2) ≤ 2 := by
  have h1 : sqrt (a + (1 / 4) * (b - c) ^ 2) ≤ (a + 1) / 2 := by
    have h2 : a + (1 / 4) * (b - c) ^ 2 ≥ 0 := by
      positivity
    have h3 : (sqrt (a + (1 / 4) * (b - c) ^ 2)) ^ 2 = a + (1 / 4) * (b - c) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith 
    have h4 : ((a + 1) / 2) ^ 2 ≥ a + (1 / 4) * (b - c) ^ 2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - 1), hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    have h5 : sqrt (a + (1 / 4) * (b - c) ^ 2) ≤ (a + 1) / 2 := by
      nlinarith [Real.sqrt_nonneg (a + (1 / 4) * (b - c) ^ 2), h3, h4]
    linarith
  have h2 : sqrt (b + (1 / 4) * (c - a) ^ 2) ≤ (b + 1) / 2 := by
    have h6 : b + (1 / 4) * (c - a) ^ 2 ≥ 0 := by 
      positivity 
    have h7 : (sqrt (b + (1 / 4) * (c - a) ^ 2)) ^ 2 = b + (1 / 4) * (c - a) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith 
    have h8 : ((b + 1) / 2) ^ 2 ≥ b + (1 / 4) * (c - a) ^ 2 := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (b - 1), hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    have h9 : sqrt (b + (1 / 4) * (c - a) ^ 2) ≤ (b + 1) / 2 := by 
      nlinarith [Real.sqrt_nonneg (b + (1 / 4) * (c - a) ^ 2), h7, h8]
    linarith 
  have h3 : sqrt (c + (1 / 4) * (a - b) ^ 2) ≤ (c + 1) / 2 := by
    have h6 : c + (1 / 4) * (a - b) ^ 2 ≥ 0 := by
      positivity
    have h7 : (sqrt (c + (1 / 4) * (a - b) ^ 2)) ^ 2 = c + (1 / 4) * (a - b) ^ 2 := by 
      rw [Real.sq_sqrt]
      linarith 
    have h8 : ((c + 1) / 2) ^ 2 ≥ c + (1 / 4) * (a - b) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (c - 1), hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    have h9 : sqrt (c + (1 / 4) * (a - b) ^ 2) ≤ (c + 1) / 2 := by 
      nlinarith [Real.sqrt_nonneg (c + (1 / 4) * (a - b) ^ 2), h7, h8]
    linarith 
  linarith [h1, h2, h3, hsum]