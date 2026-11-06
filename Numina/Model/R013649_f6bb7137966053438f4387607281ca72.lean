import Mathlib

theorem algebra_165638 (z : ℝ) (hz : z ≠ 1 ∧ z ≠ -1 ∧ z ≠ 2 ∧ z ≠ -2) :
    (z + 4) / (z - 1) + (z - 4) / (z + 1) = (z + 8) / (z - 2) + (z - 8) / (z + 2) + 6 ↔ False := by
  constructor
  · -- Assume the equation holds, prove False
    intro h
    rcases hz with ⟨hz1, hz2, hz3, hz4⟩
    have h1 : z - 1 ≠ 0 := by
      intro h'
      apply hz1
      linarith
    have h2 : z + 1 ≠ 0 := by
      intro h'
      apply hz2
      linarith
    have h3 : z - 2 ≠ 0 := by
      intro h'
      apply hz3
      linarith
    have h4 : z + 2 ≠ 0 := by
      intro h'
      apply hz4
      linarith
    field_simp [(show z - 1 ≠ 0 by assumption), (show z + 1 ≠ 0 by assumption),
      (show z - 2 ≠ 0 by assumption), (show z + 2 ≠ 0 by assumption)] at h ⊢
    nlinarith [sq_nonneg (z ^ 2 - 2), sq_nonneg (z ^ 2 - 4), sq_nonneg (z + 1), sq_nonneg (z - 1), sq_nonneg (z + 2), sq_nonneg (z - 2), sq_nonneg (z ^ 2), sq_nonneg ((z - 1) * (z + 1)), sq_pos_of_ne_zero (show (z - 1) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z + 1) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z - 2) ≠ 0 by assumption), sq_pos_of_ne_zero (show (z + 2) ≠ 0 by assumption)]
  · -- Show that False implies anything
    intro h
    cases h