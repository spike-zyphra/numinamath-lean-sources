import Mathlib

theorem algebra_275022 (x y : ℕ) (hx : x ≤ 100) (hy : y ≤ 100)
    (havg : (69 + 53 + 69 + 71 + 78 + x + y) / 7 = 66) :
    x ≥ 22 := by
  omega