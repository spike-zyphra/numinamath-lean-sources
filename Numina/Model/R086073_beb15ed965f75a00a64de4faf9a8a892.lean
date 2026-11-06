import Mathlib

open Real

theorem inequalities_114586 (x : ℝ) (hx : x > 0) :
    x + 1 / x ≥ 2 ∧ (x + 1 / x = 2 ↔ x = 1) := by
  have h1 : x + 1 / x ≥ 2 := by
    have h2 : x > 0 := hx
    have h3 : x + 1 / x - 2 ≥ 0 := by
      have h4 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
        field_simp
        ring
      rw [h4]
      have h5 : x ^ 2 + 1 - 2 * x ≥ 0 := by
        have h6 : x ^ 2 + 1 - 2 * x = (x - 1) ^ 2 := by ring
        rw [h6]
        apply sq_nonneg
      have h7 : x > 0 := hx
      have h8 : (x ^ 2 + 1 - 2 * x) / x ≥ 0 := by
        apply div_nonneg
        linarith [h5]
        linarith
      linarith
    linarith
  have h_eq : x + 1 / x = 2 ↔ x = 1 := by
    constructor
    · -- Showing that if $x + \frac{1}{x} = 2$, then $x = 1$
      intro h
      have h2 : x > 0 := hx
      have h3 : x * (x + 1 / x) = x * 2 := by
        rw [h]
      have h4 : x * (x + 1 / x) = x ^ 2 + 1 := by
        field_simp
        <;> ring
      rw [h4] at h3
      have h5 : (x - 1) ^ 2 = 0 := by
        nlinarith
      have h6 : x - 1 = 0 := by
        apply pow_eq_zero
        exact h5
      linarith
    · -- Showing that if $x = 1$, then $x + \frac{1}{x} = 2$
      intro h
      rw [h]
      norm_num
  constructor
  · exact h1
  · exact h_eq