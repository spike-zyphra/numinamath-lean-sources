import Mathlib

theorem algebra_319957 (x y z : ℝ) :
    abs (abs (x - y) + x + y - 2 * z) + abs (x - y) + x + y + 2 * z = 4 * max (max x y) z := by 
  cases' abs_cases (x - y) with h h <;> 
  cases' abs_cases (abs (x - y) + x + y - 2 * z) with h' h' <;> 
  cases' max_cases x y with hxy hxy <;> 
  cases' max_cases (max x y) z with hz hz <;> 
  all_goals 
    linarith