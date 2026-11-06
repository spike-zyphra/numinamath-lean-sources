import Mathlib

theorem algebra_208622 (x : ℝ) (hx : 3 * x - 2 ≠ 0) :
    (|x| - 2) / (3 * x - 2) < 0 ↔ (2 / 3 < x ∧ x < 2) ∨ x < -2 := by
  constructor
  · -- Forward direction: If (|x| - 2) / (3 * x - 2) < 0, then (2/3 < x ∧ x < 2) ∨ x < -2
    intro h
    have h1 : (|x| - 2) / (3 * x - 2) < 0 := h
    apply div_neg_iff.mp at h1
    cases h1 with
    | inl h2 =>
      have h3 : |x| > 2 := by linarith
      have h4 : x < 2 / 3 := by linarith
      cases abs_cases x with
      | inl h5 =>
        exfalso
        linarith
      | inr h5 =>
        have h6 : x < -2 := by linarith
        right
        exact h6
    | inr h2 =>
      have h3 : |x| < 2 := by linarith
      have h4 : x > 2 / 3 := by linarith
      cases abs_cases x with
      | inl h5 =>
        left
        constructor
        · linarith
        · linarith
      | inr h5 =>
        exfalso
        linarith
  · -- Backward direction: If (2/3 < x ∧ x < 2) ∨ x < -2, then (|x| - 2) / (3 * x - 2) < 0
    intro h
    cases h with
    | inl h1 =>
      have h2 : 2 / 3 < x := h1.1
      have h3 : x < 2 := h1.2
      have h4 : |x| = x := by
        rw [abs_of_nonneg]
        linarith
      have h5 : |x| - 2 < 0 := by
        rw [h4]
        linarith
      have h6 : 3 * x - 2 > 0 := by linarith
      apply div_neg_of_neg_of_pos
      · linarith
      · linarith
    | inr h2 =>
      have h3 : x < -2 := h2
      have h4 : |x| > 2 := by
        cases abs_cases x with
        | inl h5 =>
          linarith
        | inr h5 =>
          nlinarith
      have h5 : 3 * x - 2 < 0 := by linarith
      have h6 : |x| - 2 > 0 := by linarith
      apply div_neg_of_pos_of_neg
      · linarith
      · linarith