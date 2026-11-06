import Mathlib

theorem algebra_4777 (x y : ℤ) (h : x > 0 ∧ y > 0) (h1 : x * 99 + y * 129 = 4452) :
    (x + y) % 10 = 8 := by 
  omega