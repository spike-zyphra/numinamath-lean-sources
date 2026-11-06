import Mathlib

theorem inequalities_184805 (x : ℝ) :
    (3 * x ^ 2 + 6 * x > 9) ↔ (x > 1 ∨ x < -3) := by
  constructor
  · -- Assume 3 * x ^ 2 + 6 * x > 9, prove x > 1 ∨ x < -3
    intro h
    have h1 : 3 * x^2 + 6 * x - 9 > 0 := by linarith
    have h2 : (x - 1) * (x + 3) > 0 := by 
      nlinarith
    cases (mul_pos_iff.mp h2) with
    | inl h3 =>
      left
      linarith
    | inr h4 =>
      right
      linarith
  · -- Assume x > 1 ∨ x < -3, prove 3 * x ^ 2 + 6 * x > 9
    intro h
    cases h with
    | inl h1 =>
      nlinarith
    | inr h2 =>
      nlinarith