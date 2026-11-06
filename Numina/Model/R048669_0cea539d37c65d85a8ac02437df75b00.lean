import Mathlib

theorem inequalities_104952 (x : ℝ) (hx : x > 0) :
    x + 1 / x ≥ 2 ∧ (x + 1 / x = 2 ↔ x = 1) := by
  have h1 : x + 1 / x - 2 ≥ 0 := by
    have h2 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
      field_simp
      ring
    rw [h2]
    have h3 : x ^ 2 + 1 - 2 * x ≥ 0 := by
      nlinarith [sq_nonneg (x - 1)]
    apply div_nonneg
    · linarith
    · linarith
  have h2 : x + 1 / x ≥ 2 := by linarith [h1]
  have h3 : x + 1 / x = 2 ↔ x = 1 := by
    constructor
    · -- Assume x + 1/x = 2
      intro h_eq
      have h_eq' : x ^ 2 + 1 = 2 * x := by 
        field_simp at h_eq
        linarith
      have h_eq'' : (x - 1) ^ 2 = 0 := by 
        nlinarith
      have h_eq_1 : x - 1 = 0 := by 
        rw [sq_eq_zero_iff] at h_eq''
        linarith
      linarith
    · -- Assume x = 1
      intro h_eq
      rw [h_eq]
      norm_num
  constructor
  · exact h2
  · exact h3