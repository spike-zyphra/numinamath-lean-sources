import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_260629 :
  {x : ℝ | (x^2 - 7 * x + 12) / (x^2 - 16 * x + 63) > 0} =
  {x | x < 3 ∨ 4 < x ∧ x < 7 ∨ x > 9} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume (x^2 - 7 * x + 12) / (x^2 - 16 * x + 63) > 0, prove x < 3 ∨ 4 < x ∧ x < 7 ∨ x > 9
    intro h
    have h1 : (x^2 - 7*x + 12) / (x^2 - 16*x + 63) > 0 := h
    apply div_pos_iff.mp at h1
    cases h1 with
    | inl h2 =>
      have h3 : x^2 - 7 * x + 12 > 0 := h2.1
      have h4 : x^2 - 16 * x + 63 > 0 := h2.2
      have h7 : x < 3 ∨ x > 4 := by
        by_contra h8
        push_neg at h8
        nlinarith
      have h8 : x < 7 ∨ x > 9 := by
        by_contra h9
        push_neg at h9
        nlinarith
      cases h7 with
      | inl h9 =>
        left
        exact h9
      | inr h10 =>
        cases h8 with
        | inl h11 =>
          have : 4 < x ∧ x < 7 := by
            constructor <;> linarith
          simp [this]
        | inr h12 =>
          have h13 : x > 9 := h12
          simp [h13]
    | inr h2 =>
      have h3 : x^2 - 7 * x + 12 < 0 := h2.1
      have h4 : x^2 - 16 * x + 63 < 0 := h2.2
      nlinarith [sq_nonneg (x - 3.5), sq_nonneg (x - 8)]
  · -- Assume x < 3 ∨ 4 < x ∧ x < 7 ∨ x > 9, prove (x^2 - 7 * x + 12) / (x^2 - 16 * x + 63) > 0
    intro h
    cases h with
    | inl h1 =>
      have h2 : x < 3 := h1
      have h3 : x^2 - 7 * x + 12 > 0 := by nlinarith
      have h4 : x^2 - 16 * x + 63 > 0 := by nlinarith
      apply div_pos
      all_goals linarith
    | inr h1 =>
      cases h1 with
      | inl h2 =>
        have h3 : 4 < x := h2.1
        have h4 : x < 7 := h2.2
        have h5 : x^2 - 7 * x + 12 > 0 := by nlinarith
        have h6 : x^2 - 16 * x + 63 > 0 := by nlinarith
        apply div_pos
        all_goals nlinarith
      | inr h3 =>
        have h4 : x > 9 := h3
        have h5 : x^2 - 7 * x + 12 > 0 := by nlinarith
        have h6 : x^2 - 16 * x + 63 > 0 := by nlinarith
        apply div_pos
        all_goals nlinarith