import Mathlib


theorem algebra_9021 (x : ℝ) :
    x ^ 2 + x - 2 < 0 ↔ -2 < x ∧ x < 1 := by
  constructor
  · -- Proof of the forward direction: x^2 + x - 2 < 0 → -2 < x ∧ x < 1
    intro h
    have h1 : (x + 2) * (x - 1) < 0 := by nlinarith
    cases mul_neg_iff.mp h1 with
    | inl h2 =>
      constructor <;> linarith
    | inr h2 =>
      linarith
  · -- Proof of the reverse direction: -2 < x ∧ x < 1 → x^2 + x - 2 < 0
    rintro ⟨h1, h2⟩
    have h3 : (x + 2) * (x - 1) < 0 := by
      apply mul_neg_of_pos_of_neg
      · linarith
      · linarith
    nlinarith