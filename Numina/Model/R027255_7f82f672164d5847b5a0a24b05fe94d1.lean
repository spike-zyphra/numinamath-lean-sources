import Mathlib

theorem calculus_143646 (x y : ℝ) (h : (3 * x ^ 2 * y ^ 2 + 7) * dx + 2 * x ^ 3 * y * dy = 0)
    (hy0 : y = 1) :
    ∃ C1, y ^ 2 * x ^ 3 + 7 * C1 = 0 := by 
  use (-x^3 / 7)
  rw [hy0]
  ring