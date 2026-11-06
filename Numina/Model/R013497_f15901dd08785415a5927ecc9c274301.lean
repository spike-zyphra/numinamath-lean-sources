import Mathlib

theorem algebra_243849 (a b c d : ℝ) (h₀ : abs (a - b) = 5) (h₁ : abs (b - c) = 8) (h₂ : abs (c - d) = 10) :
    abs (a - d) ≥ 3 := by
  cases' abs_cases (a - b) with h3 h3 <;> 
    cases' abs_cases (b - c) with h4 h4 <;> 
      cases' abs_cases (c - d) with h5 h5 <;> 
        cases' abs_cases (a - d) with h6 h6 <;> 
          linarith