import Mathlib

theorem inequalities_65019 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    3 / 2 ≤ a ^ 3 / (a ^ 2 + 1) + b ^ 3 / (b ^ 2 + 1) + c ^ 3 / (c ^ 2 + 1) := by

  have h1 : a ^ 3 / (a ^ 2 + 1) ≥ (2 * a - 1) / 2 := by 
    have h1 : 0 < a ^ 2 + 1 := by
      nlinarith
    apply (le_div_iff₀ h1).mpr
    nlinarith [sq_nonneg (a - 1)]
    
  have h2 : b ^ 3 / (b ^ 2 + 1) ≥ (2 * b - 1) / 2 := by 
    have h2 : 0 < b ^ 2 + 1 := by
      nlinarith
    apply (le_div_iff₀ h2).mpr
    nlinarith [sq_nonneg (b - 1)]
    
  have h3 : c ^ 3 / (c ^ 2 + 1) ≥ (2 * c - 1) / 2 := by 
    have h3 : 0 < c ^ 2 + 1 := by
      nlinarith
    apply (le_div_iff₀ h3).mpr
    nlinarith [sq_nonneg (c - 1)]
    
  have h4 : a ^ 3 / (a ^ 2 + 1) + b ^ 3 / (b ^ 2 + 1) + c ^ 3 / (c ^ 2 + 1) ≥ (2 * a - 1) / 2 + (2 * b - 1) / 2 + (2 * c - 1) / 2 := by 
    linarith [h1, h2, h3]

  have h5 : (2 * a - 1) / 2 + (2 * b - 1) / 2 + (2 * c - 1) / 2 = 3 / 2 := by
    linarith [h]

  linarith [h4, h5]