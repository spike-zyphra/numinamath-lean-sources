import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_602709 (x y : ℝ) (h : x^2 + y^2 - 4 * x + 3 < 0) : y^2 < 3 * x := by 
  nlinarith [sq_nonneg (x - 2), sq_nonneg y]