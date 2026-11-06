import Mathlib

theorem algebra_95760 (x t : ℤ) (_ : x > 0) (ht: t > 0) (h : 30 * x + 30 * (x - t) + 30 * (x - 2 * t) + 30 * 10 / 60 * (x - 3 * t)= 1775) (v: x - 3 * t > 0) :
30 * x + 15 * (x - t) = 945 := by
  omega