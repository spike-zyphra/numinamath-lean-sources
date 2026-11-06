import Mathlib

open Real

theorem inequalities_159450 (x : ℝ) (hx : x > 0) :
    x + 1 / x ≥ 2 ∧ (x + 1 / x = 2 ↔ x = 1) := by
  have h1 : x + 1 / x ≥ 2 := by
    have h2 : x + 1 / x - 2 ≥ 0 := by
      have h3 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := by
        field_simp
        ring
      rw [h3]
      have h4 : x ^ 2 + 1 - 2 * x ≥ 0 := by
        have h5 : x ^ 2 + 1 - 2 * x = (x - 1)^2 := by
          ring
        rw [h5]
        exact sq_nonneg (x - 1)
      have h6 : (x ^ 2 + 1 - 2 * x) / x ≥ 0 := by
        apply div_nonneg
        linarith [h4]
        positivity
      linarith
    linarith
  have h2 : x + 1 / x = 2 ↔ x = 1 := by
    constructor
    · -- Assume x + 1/x = 2, prove x = 1
      intro h
      field_simp at h
      have h3 : (x - 1) ^ 2 = 0 := by
        nlinarith
      have h4 : x - 1 = 0 := by
        nlinarith [h3, sq_nonneg (x - 1)]
      linarith
    · -- Assume x = 1, prove x + 1/x = 2
      intro h
      rw [h]
      norm_num
  constructor
  · exact h1
  · exact h2