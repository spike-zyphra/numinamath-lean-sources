import Mathlib

theorem algebra_38 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h : x * 10000 + y * 10000 = 200000) (h1 : x * 40000 + y * 110000 = 40000) :
    x = 23 ∧ y = 77 := by
  omega