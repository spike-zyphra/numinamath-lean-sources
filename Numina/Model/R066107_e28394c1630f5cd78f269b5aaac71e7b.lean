import Mathlib

theorem inequalities_8363 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + b ^ 2) / (a + b) + (a ^ 2 + c ^ 2) / (a + c) + (b ^ 2 + c ^ 2) / (b + c) ≥ a + b + c := by

  have h₁ : (a ^ 2 + b ^ 2) / (a + b) ≥ (a + b) / 2 := by
    have h₁ : 0 < a + b := by linarith
    have h₂ : (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 / 2 := by 
      nlinarith [sq_nonneg (a - b)]
    have h₃ : (a ^ 2 + b ^ 2) / (a + b) ≥ (a + b) / 2 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  have h₂ : (a ^ 2 + c ^ 2) / (a + c) ≥ (a + c) / 2 := by
    have h₁ : 0 < a + c := by linarith
    have h₂ : (a ^ 2 + c ^ 2) ≥ (a + c) ^ 2 / 2 := by 
      nlinarith [sq_nonneg (a - c)]
    have h₃ : (a ^ 2 + c ^ 2) / (a + c) ≥ (a + c) / 2 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith
  
  have h₃ : (b ^ 2 + c ^ 2) / (b + c) ≥ (b + c) / 2 := by
    have h₁ : 0 < b + c := by linarith
    have h₂ : (b ^ 2 + c ^ 2) ≥ (b + c) ^ 2 / 2 := by 
      nlinarith [sq_nonneg (b - c)]
    have h₃ : (b ^ 2 + c ^ 2) / (b + c) ≥ (b + c) / 2 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith

  linarith [h₁, h₂, h₃]