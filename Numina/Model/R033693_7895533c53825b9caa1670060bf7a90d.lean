import Mathlib

open Real
open scoped BigOperators

theorem inequalities_223356 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0)
  (h₂ : c > 0) (h₃ : a^2 + b^2 = c^2) :
  (a^3 + b^3 + c^3) / (a * b * (a + b + c)) ≥ sqrt 2 := by
  have h4 : a * b * (a + b + c) > 0 := by
    have h5 : a * b > 0 := mul_pos h₀ h₁
    have h6 : a + b + c > 0 := by
      nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
    nlinarith
  have h5 : a^3 + b^3 + c^3 ≥ sqrt 2 * (a * b * (a + b + c)) := by 
    have h11 : (a^3 + b^3 + c^3) ^ 2 ≥ 2 * (a * b * (a + b + c)) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), sq_nonneg (a + b - c), sq_nonneg (a * b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a * (a + b) - b * c), sq_nonneg (b * (a + b) - a * c), sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (c - b * Real.sqrt 2), sq_nonneg (a^2 + b^2 - c^2), sq_nonneg (a * b), sq_nonneg (c * (a - b)), sq_nonneg (c^2 - 2 * a * b), sq_nonneg ((a - b) * c), sq_nonneg (a * b - a * b), sq_nonneg (a * b - c * a), sq_nonneg (a * b - c * b), sq_nonneg (c * (a - b)), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a^2 - b^2), sq_nonneg (c^2 - 2 * a * b), h₃, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
    have h12 : a^3 + b^3 + c^3 ≥ 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b, h₃, h₀, h₁, h₂]
    have h13 : sqrt 2 * (a * b * (a + b + c)) ≥ 0 := by
      have h14 : sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      have h15 : a * b * (a + b + c) > 0 := h4
      nlinarith
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (a^3 + b^3 + c^3 - sqrt 2 * (a * b * (a + b + c))), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h₁, h₀, h₂, sq_nonneg (a - b), h₃, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
  have h6 : (a^3 + b^3 + c^3) / (a * b * (a + b + c)) ≥ sqrt 2 := by 
    have h7 : (a^3 + b^3 + c^3) ≥ sqrt 2 * (a * b * (a + b + c)) := h5
    have h8 : a * b * (a + b + c) > 0 := h4
    apply (le_div_iff₀ h8).mpr
    linarith
  exact h6