import Mathlib

open Real Set

theorem algebra_187273 (x : ℝ) :
    x > 3 ∨ x < -10 ↔ ∃ y, y = x^2 + 7 * x - 30 ∧ y > 0 := by
  constructor
  · -- Forward implication: If x > 3 or x < -10, then ∃ y, y = x^2 + 7 * x - 30 ∧ y > 0
    rintro (h | h)
    · -- Case x > 3
      use x^2 + 7 * x - 30
      constructor
      · -- Show y = x^2 + 7 * x - 30
        rfl
      · -- Show y > 0
        nlinarith
    · -- Case x < -10
      use x^2 + 7 * x - 30
      constructor
      · -- Show y = x^2 + 7 * x - 30
        rfl
      · -- Show y > 0
        nlinarith
  · -- Reverse implication: If ∃ y, y = x^2 + 7 * x - 30 ∧ y > 0, then x > 3 ∨ x < -10
    rintro ⟨y, rfl, hy⟩
    have h1 : x ^ 2 + 7 * x - 30 > 0 := by linarith
    have : (x - 3) * (x + 10) > 0 := by nlinarith
    cases mul_pos_iff.mp this with
    | inl h2 =>
      left
      linarith
    | inr h3 =>
      right
      linarith