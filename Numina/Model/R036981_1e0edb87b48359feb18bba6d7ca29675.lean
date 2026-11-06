import Mathlib

theorem algebra_187747 (a b c d : ℝ) (h₁ : abs (a - b) + abs (c - d) = 99)
    (h₂ : abs (a - c) + abs (b - d) = 1) :
    abs (a - d) + abs (b - c) = 99 := by
  cases' abs_cases (a - b) with h h <;> 
    cases' abs_cases (c - d) with k k <;> 
      cases' abs_cases (a - c) with l l <;> 
        cases' abs_cases (b - d) with m m <;> 
          cases' abs_cases (a - d) with n n <;> 
            cases' abs_cases (b - c) with p p <;> 
              linarith