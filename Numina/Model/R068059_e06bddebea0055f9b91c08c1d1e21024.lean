import Mathlib

open Real

theorem inequalities_294080 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y ^ 2 / x ≥ 2 * y ∧ (x + y ^ 2 / x = 2 * y ↔ x = y) := by

  have h1 : x + y ^ 2 / x ≥ 2 * y := by
    have h2 : x + y ^ 2 / x - 2 * y ≥ 0 := by
      have h3 : x + y ^ 2 / x - 2 * y = (x - y) ^ 2 / x := by
        field_simp
        <;> nlinarith
      rw [h3]
      have h4 : (x - y) ^ 2 ≥ 0 := by
        exact sq_nonneg (x - y)
      have h5 : (x - y) ^ 2 / x ≥ 0 := by
        apply div_nonneg
        exact h4
        linarith
      linarith
    linarith

  have h2 : (x + y ^ 2 / x = 2 * y) ↔ (x = y) := by
    constructor
    · -- Assume x + y^2 / x = 2 * y, prove x = y
      intro h_eq
      have h_eq' : (x - y) ^ 2 = 0 := by
        have h6 : x ≠ 0 := by nlinarith
        field_simp [h6] at h_eq ⊢
        nlinarith [sq_nonneg (x - y)]
      have h_eq_zero : x - y = 0 := by
        apply pow_eq_zero 
        exact h_eq' 
      linarith

    · -- Assume x = y, prove x + y^2 / x = 2 * y
      intro h_eq
      rw [h_eq]
      field_simp [h_eq]
      <;> nlinarith

  constructor
  · exact h1
  · exact h2