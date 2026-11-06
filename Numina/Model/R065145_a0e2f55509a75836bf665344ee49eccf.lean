import Mathlib

open Real
open scoped BigOperators

theorem inequalities_240701 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) :
  a^4 + a^2 * b^2 + b^4 ≥ 3 / 4 * c^4 := by
  have h4 : a^2 * b^2 ≤ (c^4) / 4 := by
    have h6 : a * b ≤ c^2 / 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - c^2 / 2), sq_nonneg (a + b), sq_nonneg (a * b - c^2 / 2), sq_nonneg (a^2 - b^2), h₃, mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), mul_pos h₀ h₁]
 
    have h_nonneg : a * b ≥ 0 := mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)
    have h_sq : (a * b) ^ 2 ≤ (c^2 / 2) ^ 2 := by
      nlinarith [h_nonneg, h6, sq_nonneg (c^2 / 2 - a * b), sq_nonneg (c^2), sq_nonneg (a * b), sq_nonneg (c^2 - 2 * a * b), sq_nonneg (a^2 - b^2), pow_two_nonneg (a * b - c^2 / 2), h₃, mul_pos h₀ h₁]

    linarith [h_sq, sq_nonneg (c^2)]
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 * b^2 - c^4 / 4), sq_nonneg (a^2 + b^2 - c^2), h₃, sq_nonneg (a * b - c^2 / 2), sq_nonneg (a^4 + b^4 - c^4), mul_pos h₀ h₁, mul_nonneg (show (0 : ℝ) ≤ a^2 by nlinarith) (show (0 : ℝ) ≤ b^2 by nlinarith), mul_nonneg (show (0 : ℝ) ≤ a^2 by nlinarith) (show (0 : ℝ) ≤ c^2 by nlinarith), mul_nonneg (show (0 : ℝ) ≤ b^2 by nlinarith) (show (0 : ℝ) ≤ c^2 by nlinarith), h4, sq_nonneg (a^2 - b^2), sq_nonneg (a * b - c^2 / 2), sq_nonneg (a + b), sq_nonneg (a - b)]
  <;> nlinarith
  <;> try { tauto }
  <;> try { assumption }
  <;> try { nlinarith }
  <;> try { 
    norm_num
    <;> try { assumption }
  } <;> try { assumption }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { 
    norm_num
    <;> try { assumption }
  }