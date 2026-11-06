import Mathlib

theorem algebra_21610
    (flick fleck flock : ℝ)
    (h₀ : 3 * flick = 8 * fleck)
    (h₁ : 6 * flock = 4 * fleck) :
    12 * flick = 48 * flock := by
  linarith [h₀, h₁]