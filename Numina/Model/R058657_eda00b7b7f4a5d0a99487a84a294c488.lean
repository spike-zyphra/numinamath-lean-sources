import Mathlib

theorem inequalities_106209 (a b : ℝ) : a + b < a * b + 1 ↔ (a > 1 ∧ b > 1) ∨ (a < 1 ∧ b < 1) := by
  constructor
  · -- Forward direction: $a + b < a * b + 1$ implies $(a > 1 ∧ b > 1) ∨ (a < 1 ∧ b < 1)$
    intro h
    have h1 : (a - 1) * (b - 1) > 0 := by
      nlinarith
    cases (mul_pos_iff.mp h1) with
    | inl h2 =>
      left
      constructor
      · linarith
      · linarith
    | inr h3 =>
      right
      constructor
      · linarith
      · linarith
  · -- Backward direction: $(a > 1 ∧ b > 1) ∨ (a < 1 ∧ b < 1)$ implies $a + b < a * b + 1$
    rintro (h | h)
    · -- Case $(a > 1 ∧ b > 1)$
      have h1 : (a - 1) * (b - 1) > 0 := by
        apply mul_pos
        linarith
        linarith
      nlinarith
    · -- Case $(a < 1 ∧ b < 1)$
      have h1 : (a - 1) * (b - 1) > 0 := by
        apply mul_pos_of_neg_of_neg
        linarith
        linarith
      nlinarith