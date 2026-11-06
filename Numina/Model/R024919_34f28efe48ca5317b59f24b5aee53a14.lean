import Mathlib

theorem algebra_91833 {a b : ℝ} (h₁ : ∃ x, x^2 + 6 * x + 4 * a = 0 ∧ x^2 + 2 * b * x - 12 = 0) :
    ∃ x, x^2 + 9 * x + 9 * a = 0 ∧ x^2 + 3 * b * x - 27 = 0 := by
  rcases h₁ with ⟨x, h1, h2⟩
  use (3 * x / 2)
  constructor
  · -- Show that (3 * x / 2) is a solution to x^2 + 9 * x + 9 * a = 0.
    have eq3 : (3 * x / 2) ^ 2 + 9 * (3 * x / 2) + 9 * a = 0 := by
      ring_nf
      nlinarith [h1]
    linarith 
  · -- Show that (3 * x / 2) is a solution to x^2 + 3 * b * x - 27 = 0.
    have eq4 : (3 * x / 2) ^ 2 + 3 * b * (3 * x / 2) - 27 = 0 := by
      ring_nf
      nlinarith [h2]
    linarith