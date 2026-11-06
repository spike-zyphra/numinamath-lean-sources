import Mathlib
theorem algebra_607258 (x y : ℝ) : |x| + |y| ≤ |x - y| + |x + y|:= by 
  cases' abs_cases x with hx hx <;> 
  cases' abs_cases y with hy hy <;> 
  cases' abs_cases (x - y) with hxy hxy <;> 
  cases' abs_cases (x + y) with hxy1 hxy1 <;> 
  all_goals
    linarith