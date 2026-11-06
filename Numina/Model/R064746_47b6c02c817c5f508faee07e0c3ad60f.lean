import Mathlib

open Real

theorem inequalities_142229 (x : ℝ) (hx : 0 < x) :
    x + 1 / x ≥ 2 ∧ (x + 1 / x = 2 ↔ x = 1) := by
  have h1 : x + 1 / x ≥ 2 := by 
    have h2 : x + 1 / x - 2 ≥ 0 := by 
      have h3 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by 
        field_simp 
        ring
      rw [h3]
      have h4 : x ^ 2 + 1 - 2 * x ≥ 0 := by 
        nlinarith [sq_nonneg (x - 1)]
      have h5 : x > 0 := by linarith
      apply div_nonneg 
      linarith 
      linarith 
    linarith 
  have h_eq : x + 1 / x = 2 ↔ x = 1 := by 
    constructor 
    · -- Forward direction: Assume x + 1/x = 2 prove x = 1 
      intro h_eq
      have h4 : x ^ 2 + 1 - 2 * x = 0 := by 
        have h3 : x + 1 / x = 2 := h_eq 
        field_simp at h3 
        nlinarith 
      have h4' : (x - 1) ^ 2 = 0 := by 
        nlinarith 
      have h5 : x - 1 = 0 := by 
        simp [sq_eq_zero_iff] at h4' ⊢ 
        exact h4' 
      linarith 
    · -- Backward direction: Assume x = 1 prove x + 1/x = 2 
      intro h_eq 
      rw [h_eq] 
      norm_num 
  constructor 
  · exact h1 
  · exact h_eq