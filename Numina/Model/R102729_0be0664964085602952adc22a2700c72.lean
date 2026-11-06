import Mathlib

theorem algebra_157749 (x y z : ℝ) (hx : x ≥ 45) (hy : y ≥ 60) (hz : z ≥ 5)
    (h1 : 30 * x + 50 * y = 45 * z) (h2 : 10 * x + 10 * y = 45 * z)
    (h3 : 20 * y + 5 * z = 60 * z) :
    x = 3 ∧ y = 2 ∧ z = 1 := by
  linarith