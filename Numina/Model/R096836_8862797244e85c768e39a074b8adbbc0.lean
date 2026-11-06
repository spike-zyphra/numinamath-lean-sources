import Mathlib

theorem algebra_194495 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : 48 * x = 27 * y) (h2 : 27 * (x - 6) = 48 * y) :
    x = 1824 := by
  omega