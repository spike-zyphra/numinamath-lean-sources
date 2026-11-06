import Mathlib

open Real

theorem inequalities_255924 (y : ℝ) (hy : 0 < y) :
    2 * y ≥ 3 - 1 / y^2 ∧ (2 * y = 3 - 1 / y^2 ↔ y = 1) := by
  constructor
  · -- First, we prove that 2 * y ≥ 3 - 1 / y^2 for all positive y
    have h1 : 0 < y^2 := by
      nlinarith [sq_pos_of_pos hy]
    have h2 : 2 * y ≥ 3 - 1 / y^2 := by
      have h3 : 2 * y^3 ≥ 3 * y^2 - 1 := by
        nlinarith [sq_nonneg (y - 1), sq_nonneg (y + 1 / 2), sq_nonneg (2 * y - 1), mul_pos hy hy, sq_pos_of_pos hy]
      have h6 : 2 * y - (3 - 1 / y^2) ≥ 0 := by
        have h8 : y^2 > 0 := by
          nlinarith [sq_pos_of_pos hy]
        have h9 : 2 * y^3 - 3 * y^2 + 1 ≥ 0 := by
          nlinarith [h3]
        have h11 : (2 * y^3 - 3 * y^2 + 1) / y^2 ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals nlinarith
        have h12 : (2 * y^3 - 3 * y^2 + 1) / y^2 = 2 * y - (3 - 1 / y^2) := by
          field_simp
          <;> nlinarith
        linarith [h12, h11]
      linarith
    exact h2
  · -- Next, we prove when equality occurs.
    constructor
    · -- Assume equality holds, prove y = 1
      intro heq
      have h1 : 0 < y^2 := by
        exact sq_pos_of_pos hy
      have heq1 : 2 * y^3 = 3 * y^2 - 1 := by
        have h1' : 0 < y^2 := by
          exact sq_pos_of_pos hy
        field_simp [h1'] at heq ⊢
        nlinarith
      have heq2 : (y - 1)^2 * (2 * y + 1) = 0 := by
        nlinarith [heq1]
      cases' (mul_eq_zero.mp heq2) with h1 h2
      · -- Case 1: (y - 1)^2 = 0
        have h3 : y - 1 = 0 := by
          have h4 : (y - 1)^2 = 0 := by
            nlinarith
          simp at h4
          linarith
        linarith
      · -- Case 2: 2 * y + 1 = 0
        have h3 : y = -1 / 2 := by linarith
        linarith [show y > 0 from hy, show y ≥ 0 from by nlinarith]
    · -- Assume y = 1, prove equality
      intro heq
      rw [heq]
      norm_num