import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_10311 (a : ℝ) :
  {x | (a - 2) * x^2 + 2 * (a - 2) * x + 4 < 0} = ∅ ↔ 2 ≤ a ∧ a ≤ 6 := by
  have h1 : {x | (a - 2) * x^2 + 2 * (a - 2) * x + 4 < 0} = ∅ ↔ ∀ x : ℝ, ¬ ((a - 2) * x^2 + 2 * (a - 2) * x + 4 < 0) := by
    simp [Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
  rw [h1]
  constructor
  · -- If {x | (a - 2) * x^2 + 2 * (a - 2) * x + 4 < 0} = ∅, then 2 ≤ a ∧ a ≤ 6.
    intro h
    have h2 : ∀ x : ℝ, (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 ≥ 0 := by
      intro x
      have h3 : ¬ ((a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 < 0) := h x
      linarith
    have h3 : a ≤ 6 := by
      by_contra h3a
      push_neg at h3a
      have h4 : ∃ x : ℝ, (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 < 0 := by
        use -1
        nlinarith
      rcases h4 with ⟨x, hx⟩
      have hx3 : ¬ ((a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 ≥ 0) := by linarith
      have hx4 : (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 ≥ 0 := h2 x
      linarith
    have h4 : 2 ≤ a := by
      by_contra h3a
      push_neg at h3a
      have h4 : ∃ x : ℝ, (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 < 0 := by
        use -4 / (a - 2)
        have ha3 : a - 2 < 0 := by nlinarith
        have ha4 : (a - 2) * (-4 / (a - 2)) ^ 2 + 2 * (a - 2) * (-4 / (a - 2)) + 4 < 0 := by
          have ha5 : (a - 2) * (-4 / (a - 2)) ^ 2 + 2 * (a - 2) * (-4 / (a - 2)) + 4 =
              (16 - 4 * (a - 2)) / (a - 2) := by
            field_simp [show a - 2 ≠ 0 by nlinarith]
            <;> ring
          rw [ha5]
          apply div_neg_of_pos_of_neg
          · -- Show numerator is positive.
            nlinarith
          · -- Show denominator is negative.
            nlinarith
        linarith
      rcases h4 with ⟨x, hx⟩
      have hx3 : (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 ≥ 0 := h2 x
      linarith
    constructor
    · linarith
    · linarith
  · -- If 2 ≤ a ∧ a ≤ 6, then {x | (a - 2) * x^2 + 2 * (a - 2) * x + 4 < 0} = ∅.
    rintro ⟨ha1, ha2⟩
    intro x
    have h3 : (a - 2) * x ^ 2 + 2 * (a - 2) * x + 4 ≥ 0 := by
      by_cases ha4 : a - 2 > 0
      · -- a - 2 > 0
        have ha5 : 4 * (a - 2) ^ 2 - 16 * (a - 2) ≤ 0 := by
          nlinarith [sq_nonneg (a - 6)]
        nlinarith [sq_nonneg (x + 1), sq_nonneg ( (a - 2) * (x + 1) ) ]
      · -- a - 2 ≤ 0
        have ha7 : a - 2 ≤ 0 := by nlinarith
        have ha8 : a - 2 = 0 := by nlinarith
        rw [show a - 2 = (0 : ℝ) by linarith [ha8]]
        nlinarith
    linarith