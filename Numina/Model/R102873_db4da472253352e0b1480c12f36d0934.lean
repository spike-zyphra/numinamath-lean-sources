import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_113849 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (h : 2 / x + 3 / y = 2) :
  x * y ≥ 6 := by
  have h1 : 2 * y + 3 * x = 2 * x * y := by
    field_simp at h
    nlinarith
  
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), 
          mul_pos hx hy, 
          h1
  ]