import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_191980 (x : ℝ) :
  ∃ a ∈ Icc (-1) 2, (2 - a) * x^3 + (1 - 2 * a) * x^2 - 6 * x + 5 + 4 * a - a^2 < 0 ↔
  x < -2 ∨ x > 1 := by
  by_cases h : x < -2
  · -- If x < -2, pick a = -1
    use -1
    constructor
    · -- Show that -1 is in the interval [-1, 2]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show bi-implication
      constructor
      · intro h1
        left
        nlinarith
      · intro h2
        rcases h2 with h3 | h4
        · -- x < -2
          nlinarith
        · -- x > 1
          nlinarith
  · -- x ≥ -2
    use 2
    constructor
    · -- Show that 2 is in the interval [-1, 2]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show bi-implication
      constructor
      · intro h1
        have h4 : x > 1 := by
          nlinarith
        right
        linarith
      · intro h2
        rcases h2 with h3 | h4
        · -- x < -2
          nlinarith
        · -- x > 1
          nlinarith