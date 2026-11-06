import Mathlib

theorem inequalities_250091 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a ^ 4 + b ^ 4 + c ^ 4 ≤ 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) :
    a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ a ^ 2 + b ^ 2 + c ^ 2 ≤ 2 * (a * b + b * c + c * a) := by 
  constructor
  · -- Prove a ≤ b + c
    have h2 : a ^ 2 ≤ (b + c) ^ 2 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2 - c ^ 2), sq_nonneg (a - b - c), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (a - b), sq_nonneg (c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
    have h3 : a ≤ b + c := by
      nlinarith [show 0 ≤ (b + c : ℝ) by linarith, h2]
    linarith
  constructor
  · -- Prove b ≤ a + c
    have h4 : b ^ 2 ≤ (a + c) ^ 2 := by
      nlinarith [sq_nonneg (b ^ 2 - a ^ 2 - c ^ 2), sq_nonneg (b - a - c), sq_nonneg (b + a - c), sq_nonneg (b - a + c), sq_nonneg (b - a), sq_nonneg (c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
    have h5 : b ≤ a + c := by
      nlinarith [show 0 ≤ (a + c : ℝ) by linarith, h4]
    linarith
  constructor
  · -- Prove c ≤ a + b
    have h6 : c ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [sq_nonneg (c ^ 2 - a ^ 2 - b ^ 2), sq_nonneg (c - a - b), sq_nonneg (c + a - b), sq_nonneg (c - a + b), sq_nonneg (c - a), sq_nonneg (b), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
    have h7 : c ≤ a + b := by
      nlinarith [show 0 ≤ (a + b : ℝ) by linarith, h6]
    linarith
  · -- Prove a ^ 2 + b ^ 2 + c ^ 2 ≤ 2 * (a * b + b * c + c * a)
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]