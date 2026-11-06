import Mathlib

theorem algebra_196728 (x y : ℕ) (hx : x = 3) (hy : y = 0)
    (hxy : x = x + 2) (hyx : y = y + x) (h : y ≥ 10000) :
    x = 201 := by 
  omega