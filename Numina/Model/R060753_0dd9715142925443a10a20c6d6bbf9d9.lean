import Mathlib

theorem inequalities_8446 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b ^ 2 + c ^ 2) / (b + c) + (a ^ 2 + b ^ 2) / (a + b) + (c ^ 2 + a ^ 2) / (c + a) ≥ a + b + c := by
  have h1 : (b ^ 2 + c ^ 2) / (b + c) ≥ (b + c) / 2 := by
    have h2 : 0 < b + c := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (b - c)]
    
  have h2 : (a ^ 2 + b ^ 2) / (a + b) ≥ (a + b) / 2 := by
    have h3 : 0 < a + b := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (a - b)]
    
  have h3 : (c ^ 2 + a ^ 2) / (c + a) ≥ (c + a) / 2 := by
    have h4 : 0 < c + a := by linarith
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (c - a)]
    
  linarith [h1, h2, h3]