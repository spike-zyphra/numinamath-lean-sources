import Mathlib

theorem algebra_299799 (x y : ℝ) (h : abs x + abs y ≤ 1) :
    x^2 - x * y + y^2 ≤ 1 := by 
  cases' abs_cases x with hx hx <;> cases' abs_cases y with hy hy <;> 
    all_goals 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]