import Mathlib

theorem algebra_203277 {x y : ℕ} (hx : x % 3 = 0) (hy : y % 5 = 0)
    (hxy : x / 3 + 12 = y / 5) (hxy' : x / 3 = y / 5 + 6) :
    x = 72 := by
  omega