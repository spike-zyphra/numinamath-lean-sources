import Mathlib

theorem inequalities_7792 (a b c : ℝ) :
    abs a + abs b + abs c - abs (a + b) - abs (b + c) - abs (c + a) + abs (a + b + c) ≥ 0 := by 
  cases' abs_cases a <;> cases' abs_cases b <;> cases' abs_cases c <;> 
    cases' abs_cases (a + b) <;> cases' abs_cases (b + c) <;> cases' abs_cases (c + a) <;> 
      cases' abs_cases (a + b + c) <;> all_goals
        linarith