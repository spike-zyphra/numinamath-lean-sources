import Mathlib

open Real

theorem inequalities_243717 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * (b - c) ^ 2 ≥ 0 ∧ b * (c - a) ^ 2 ≥ 0 ∧ c * (a - b) ^ 2 ≥ 0 ∧
    a * (b ^ 2 - 2 * b * c + c ^ 2) + b * (c ^ 2 - 2 * a * c + a ^ 2) +
    c * (a ^ 2 - 2 * a * b + b ^ 2) ≥ 0 ∧
    a * b ^ 2 - 2 * a * b * c + a * c ^ 2 + b * c ^ 2 - 2 * a * b * c + b * a ^ 2 + c * a ^ 2 - 2 * a * b * c + c * b ^ 2 ≥
    0 ∧
    a * b ^ 2 + b * a ^ 2 + b * c ^ 2 + c * b ^ 2 + a * c ^ 2 + c * a ^ 2 ≥ 6 * a * b * c ∧
    a * b * (a + b) + b * c * (b + c) + a * c * (a + c) ≥ 6 * a * b * c := by 
  constructor
  · -- Show that a * (b - c) ^ 2 ≥ 0 
    have h1 : a * (b - c) ^ 2 ≥ 0 := by
      have h2 : (b - c) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      nlinarith
    linarith
  constructor
  · -- Show that b * (c - a) ^ 2 ≥ 0 
    have h1 : b * (c - a) ^ 2 ≥ 0 := by 
      have h2 : (c - a) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      nlinarith
    linarith
  constructor
  · -- Show that c * (a - b) ^ 2 ≥ 0 
    have h1 : c * (a - b) ^ 2 ≥ 0 := by 
      have h2 : (a - b) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      nlinarith
    linarith
  constructor
  · -- Show that a * (b ^ 2 - 2 * b * c + c ^ 2) + b * (c ^ 2 - 2 * a * c + a ^ 2) + c * (a ^ 2 - 2 * a * b + b ^ 2) ≥ 0 
    nlinarith [sq_nonneg (a * (b - c)), sq_nonneg (b * (c - a)), sq_nonneg (c * (a - b)), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  constructor
  · -- Show that a * b ^ 2 - 2 * a * b * c + a * c ^ 2 + b * c ^ 2 - 2 * a * b * c + b * a ^ 2 + c * a ^ 2 - 2 * a * b * c + c * b ^ 2 ≥ 0 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * (b - c)), sq_nonneg (b * (c - a)), sq_nonneg (c * (a - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  constructor
  · -- Show that a * b ^ 2 + b * a ^ 2 + b * c ^ 2 + c * b ^ 2 + a * c ^ 2 + c * a ^ 2 ≥ 6 * a * b * c 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Show that a * b * (a + b) + b * c * (b + c) + a * c * (a + c) ≥ 6 * a * b * c 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]