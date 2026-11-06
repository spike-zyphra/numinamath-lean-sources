import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_15354 (p : ℝ × ℝ × ℝ) (hp : p = (1, 1, 1)) :
    (p.1 * (-1), p.2.1, p.2.2) = (-1, 1, 1) := by 
  rw [hp]
  norm_num