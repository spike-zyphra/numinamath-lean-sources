import Mathlib

theorem algebra_266219 {x y : ℕ} (hx : 17 * 30 = x * 30 + y * 17) (hy : 19 * 20 = x * 20 + y * 19)
    (hxy : x * 5 + y * 3 = y * 2 + x * 2) :
    x = 31 := by
  omega