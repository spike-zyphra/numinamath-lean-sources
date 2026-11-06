import Mathlib

theorem inequalities_204995 (x y z : ℝ) (h₀ : |x| < |y - z|) (h₁ : |y| < |z - x|) :
    |z| ≥ |x - y| := by
  cases' abs_cases x with hx hx <;> 
    cases' abs_cases y with hy hy <;> 
      cases' abs_cases z with hz hz <;> 
        cases' abs_cases (x - y) with h3 h3 <;> 
          cases' abs_cases (y - z) with h4 h4 <;> 
            cases' abs_cases (z - x) with h5 h5 <;> 
              all_goals 
                try { linarith }