import Mathlib

theorem algebra_134562 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x * 35 = y * 15) (h2 : x * 15 = y * 35) :
    x * 21 = y * 35 := by
  omega