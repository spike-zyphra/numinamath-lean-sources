import Mathlib

open Real

theorem inequalities_114592 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y^2 / x ≥ 2 * y ∧ (x + y^2 / x = 2 * y ↔ x = y) := by
  have h1 : x + y^2 / x - 2 * y ≥ 0 := by
    have h2 : x + y^2 / x - 2 * y = (x - y) ^ 2 / x := by
      field_simp
      ring
    rw [h2]
    have h3 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
    have h4 : (x - y) ^ 2 / x ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals linarith
    linarith
  constructor
  · linarith
  · constructor
    · -- Assume x + y^2 / x = 2 * y prove x = y
      intro h_eq
      have h_eq2 : x + y^2 / x - 2 * y = 0 := by linarith
      have h_eq3 : (x - y) ^ 2 / x = 0 := by
        have : x + y^2 / x - 2 * y = (x - y) ^ 2 / x := by
          field_simp
          ring
        linarith [h_eq2, this]
      have h_eq4 : (x - y) ^ 2 = 0 := by
        have hx2 : x ≠ 0 := by linarith
        field_simp at h_eq3 ⊢
        nlinarith
      have h_eq5 : x - y = 0 := by
        rw [sq_eq_zero_iff] at h_eq4
        exact h_eq4
      linarith
    · -- Assume x = y prove x + y^2 / x = 2 * y
      intro h_eq
      rw [show x = y by linarith [h_eq]]
      field_simp
      <;> nlinarith