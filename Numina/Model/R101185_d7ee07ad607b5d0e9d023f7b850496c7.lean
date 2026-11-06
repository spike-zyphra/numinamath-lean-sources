import Mathlib

theorem inequalities_280139 (x y z : ℝ) :
    abs x + abs y + abs z ≤ abs (x + y - z) + abs (x - y + z) + abs (-x + y + z) := by
  cases' abs_cases x <;> cases' abs_cases y <;> cases' abs_cases z <;> 
    cases' abs_cases (x + y - z) <;> cases' abs_cases (x - y + z) <;> 
      cases' abs_cases (-x + y + z) <;> all_goals 
        linarith