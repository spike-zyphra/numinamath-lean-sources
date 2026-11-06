import Mathlib

theorem algebra_325028 {x y : ℕ} (hx : x ≤ 214) (hy : y ≤ 214)
    (hxy : x + y = 214) (h : 5 * x = 3 * y) :
    x = 137 := by
  omega