import Mathlib

theorem algebra_219666 (x y z : ℝ) (h₀ : (x - 1)/2 = -y/3) (h₁ : -y/3 = 3 - z)
    (h₂ : 4 * x + 5 * z - 3 = 0) (h₃ : 2 * x + y + 2 * z = 0) :
    2 * x - y + 7 * z - 23 = 0 := by
  linarith