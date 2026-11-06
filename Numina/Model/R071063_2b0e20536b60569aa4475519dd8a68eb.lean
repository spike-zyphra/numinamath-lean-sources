import Mathlib

theorem algebra_325071 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 45 = y * 30) (h2 : x * 25 = y * 20 + 80 / 100 * y) :
    x ≥ 5 := by
  omega