import Mathlib

open Real

theorem inequalities_114715 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / y + y / x ≥ 2 ∧ (x / y + y / x = 2 ↔ x = y) := by

  have h1 : x / y + y / x - 2 ≥ 0 := by
    have h2 : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by 
      field_simp 
      ring 
    rw [h2]
    have h3 : (x - y) ^ 2 ≥ 0 := by 
      exact sq_nonneg (x - y)
    have h4 : x * y > 0 := mul_pos hx hy
    exact div_nonneg h3 (by positivity)

  have h_eq : x / y + y / x = 2 ↔ x = y := by
    constructor
    · -- Assume x / y + y / x = 2, we need to prove x = y
      intro h_eq2
      have h2 : (x - y) ^ 2 = 0 := by
        have h3 : x / y + y / x - 2 = 0 := by linarith
        have h4 : (x - y) ^ 2 / (x * y) = 0 := by 
          have h2_eq : x / y + y / x - 2 = (x - y) ^ 2 / (x * y) := by 
            field_simp 
            ring 
          linarith [h3, h2_eq]
        have h5 : (x - y) ^ 2 = 0 := by 
          have h6 : x * y > 0 := mul_pos hx hy 
          have : (x - y) ^ 2 = 0 := by 
            field_simp at h4 ⊢ 
            nlinarith 
          assumption 
        assumption
      have h8 : x - y = 0 := by 
        rw [sq_eq_zero_iff] at h2 
        exact h2
      linarith
    · -- Assume x = y, prove x / y + y / x = 2 
      intro h_eq2 
      rw [show x = y by linarith [h_eq2]]
      have h1 : x ≠ 0 := by nlinarith 
      field_simp [h1] 
      all_goals nlinarith

  have h_ineq : x / y + y / x ≥ 2 := by linarith [h1]

  exact ⟨h_ineq, h_eq⟩