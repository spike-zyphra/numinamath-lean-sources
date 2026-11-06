import Mathlib

theorem number_theory_323557 (x y z : ℕ) (h₀ : x < 10) (h₁ : y < 10) (h₂ : z < 10)
    (h₃ : (10 * x + y) * (300 + 10 * y + z) = 29400) : x + y + z = 18 := by
  interval_cases x <;> interval_cases y <;> omega