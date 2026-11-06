import Mathlib

theorem inequalities_241820 (x y z : ℝ) :
    abs x + abs y + abs z ≤ abs (x + y - z) + abs (x - y + z) + abs (-x + y + z) := by
  cases' abs_cases x with hx hx <;> 
  cases' abs_cases y with hy hy <;> 
  cases' abs_cases z with hz hz <;> 
  cases' abs_cases (x + y - z) with h1 h1 <;> 
  cases' abs_cases (x - y + z) with h2 h2 <;> 
  cases' abs_cases (-x + y + z) with h3 h3 <;> 
  all_goals 
    linarith