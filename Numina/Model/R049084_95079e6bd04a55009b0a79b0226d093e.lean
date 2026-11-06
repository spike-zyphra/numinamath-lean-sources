import Mathlib

theorem algebra_112259 (a b c : ℝ) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    ∃ d, b = a + d ∧ c = b + d ↔ a^2 + b^2 + c^2 - a * b - b * c - c * a = 3 * (a - b) * (b - c) := by
  use b - a
  constructor
  · -- Assume (b = a + d ∧ c = b + d), prove (a^2 + b^2 + c^2 - a * b - b * c - c * a = 3 * (a - b) * (b - c))
    rintro ⟨h₁, h₂⟩
    nlinarith
  · -- Assume (a^2 + b^2 + c^2 - a * b - b * c - c * a = 3 * (a - b) * (b - c)), prove (b = a + d ∧ c = b + d)
    intro h_eq
    constructor
    · -- b = a + d is trivial as d = b - a
      linarith
    · -- c = b + d
      nlinarith