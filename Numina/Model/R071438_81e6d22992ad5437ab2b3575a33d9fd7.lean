import Mathlib

theorem inequalities_271373 (a b c : ℝ) (h₀ : a + b ≥ 0) (h₁ : b + c ≥ 0)
    (h₂ : c + a ≥ 0) :
    a + b + c ≥ (|a| + |b| + |c|) / 3 := by 
  cases' abs_cases a <;> cases' abs_cases b <;> cases' abs_cases c <;> 
    all_goals
      nlinarith