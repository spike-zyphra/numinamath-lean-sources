import Mathlib

theorem algebra_624531 {a₀ a₁ x : ℝ} (hx : x = 1) :
    a₀ * x ^ 10 - a₁ * x ^ 9 + a₀ * x ^ 8 - a₁ * x ^ 7 - a₁ * x ^ 6 + a₁ * x ^ 5 - a₀ * x ^ 4 + a₁ * x ^ 3 - a₀ * x ^ 2 + a₁ * x = 0 := by
  rw [hx]
  ring