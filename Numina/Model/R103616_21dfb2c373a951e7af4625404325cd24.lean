import Mathlib

theorem inequalities_326113 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 3 / (a ^ 2 + a * b + b ^ 2) + b ^ 3 / (b ^ 2 + b * c + c ^ 2) +
     c ^ 3 / (c ^ 2 + c * a + a ^ 2)) ≥ (a + b + c) / 3 := by 
  have h₁ : a ^ 3 / (a ^ 2 + a * b + b ^ 2) ≥ (2 * a - b) / 3 := by 
    have h₁₁ : 0 < a ^ 2 + a * b + b ^ 2 := by 
      positivity 
    apply (le_div_iff₀' h₁₁).mpr 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - a)]
  have h₂ : b ^ 3 / (b ^ 2 + b * c + c ^ 2) ≥ (2 * b - c) / 3 := by 
    have h₂₁ : 0 < b ^ 2 + b * c + c ^ 2 := by 
      positivity 
    apply (le_div_iff₀' h₂₁).mpr 
    nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (c - b)]
  have h₃ : c ^ 3 / (c ^ 2 + c * a + a ^ 2) ≥ (2 * c - a) / 3 := by 
    have h₃₁ : 0 < c ^ 2 + c * a + a ^ 2 := by 
      positivity 
    apply (le_div_iff₀' h₃₁).mpr 
    nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (a - c)]
  linarith