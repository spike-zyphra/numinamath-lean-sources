import Mathlib

theorem algebra_186987 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x * 3 + y * 2 = 87) (h2 : x * 5 + y * 3 = 94) :
    x = 30 := by 
  omega