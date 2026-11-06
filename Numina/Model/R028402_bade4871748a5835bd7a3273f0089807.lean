import Mathlib

theorem inequalities_154508 (x y z : ℝ) : |x| + |y| + |z| ≤ |x + y - z| + |y + z - x| + |z + x - y| := by
  cases' abs_cases x with hx hx <;> cases' abs_cases y with hy hy <;> cases' abs_cases z with hz hz <;> 
    cases' abs_cases (x + y - z) with h1 h1 <;> 
      cases' abs_cases (y + z - x) with h2 h2 <;> 
        cases' abs_cases (z + x - y) with h3 h3 <;> 
          all_goals 
            linarith