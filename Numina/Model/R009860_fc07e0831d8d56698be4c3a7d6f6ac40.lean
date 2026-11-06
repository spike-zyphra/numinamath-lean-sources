import Mathlib

theorem algebra_11102 (a : ℝ) (h : ∃ b, ∀x, (9 * x ^ 2 + 24 * x + a) = (b + 3 * x) ^ 2) :
    a = 16 := by
  rcases h with ⟨b, hb⟩
  have eqn1 := hb 0
  have eqn2 := hb 1
  have eqn3 := hb (-1)
  nlinarith