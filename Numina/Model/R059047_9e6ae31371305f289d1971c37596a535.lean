import Mathlib

open Real

theorem inequalities_115902 (a : ℝ) (ha : 0 < a) : a + 1 / a ≥ 2 ∧
    (a + 1 / a = 2 ↔ a = 1) := by
  have h1 : a + 1 / a - 2 ≥ 0 := by
    have h2 : a + 1 / a - 2 = (a - 1) ^ 2 / a := by
      field_simp
      ring
    rw [h2]
    have h3 : (a - 1) ^ 2 ≥ 0 := by
      exact sq_nonneg (a - 1)
    have h4 : (a - 1) ^ 2 / a ≥ 0 := by
      apply div_nonneg
      exact h3
      linarith
    linarith

  constructor
  · linarith [show a + 1/a - 2 ≥ 0 by linarith [h1]]
  · -- Proof of (a + 1/a = 2 ↔ a = 1)
    constructor
    · -- Assume a + 1/a = 2, prove a = 1
      intro h
      have h3 : a ^ 2 + 1 = 2 * a := by
        field_simp at h
        nlinarith
      have h4 : (a - 1) ^ 2 = 0 := by
        nlinarith
      have h5 : a - 1 = 0 := by
        rw [sq_eq_zero_iff] at h4
        exact h4
      linarith
    · -- Assume a = 1, prove a + 1/a = 2
      intro h
      rw [h]
      norm_num