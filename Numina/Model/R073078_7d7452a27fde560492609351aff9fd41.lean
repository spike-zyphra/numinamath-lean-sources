import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_321811 (a : ℝ) :
  (∀ x y, |x| + |y| ≤ 1 → |2 * x - 3 * y + 3 / 2| + |y - 1| + |2 * y - x - 3| ≤ a) ↔
  a ≥ 23 / 2 := by
    constructor
    · -- First direction: If the inequality holds for all x,y with |x| + |y| ≤ 1, then a ≥ 23/2.
      intro h
      have h1 := h 0 (-1 : ℝ) (by norm_num [abs_of_nonneg, abs_of_nonpos])
      norm_num [abs_of_nonneg, abs_of_nonpos] at h1
      linarith
    · -- Second direction: If a ≥ 23/2, then the inequality holds for all x, y with |x| + |y| ≤ 1.
      intro ha x y h
      cases' abs_cases (2 * x - 3 * y + 3 / 2) with h1 h1 <;> 
      cases' abs_cases (y - 1) with h2 h2 <;> 
      cases' abs_cases (2 * y - x - 3) with h3 h3 <;> 
      cases' abs_cases x with hx hx <;> 
      cases' abs_cases y with hy hy <;> 
      linarith