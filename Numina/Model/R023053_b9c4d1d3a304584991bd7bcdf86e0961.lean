import Mathlib

open Real

theorem inequalities_294115 (x y : ℝ) : abs x + abs y ≤ abs (x - y) + abs (x + y) := by 
  cases' abs_cases x with hx hx <;> cases' abs_cases y with hy hy <;> 
    cases' abs_cases (x - y) with hxy hxy <;> 
      cases' abs_cases (x + y) with hxy1 hxy1 <;> linarith