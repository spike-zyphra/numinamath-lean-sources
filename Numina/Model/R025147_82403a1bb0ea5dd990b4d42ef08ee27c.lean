import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_221570 :
  IsLeast {a : ℝ | ∀ x y : ℝ, |x| + |y| ≤ 1 → |2*x-3*y+3/2| + |y-1| + |2*y-x-3| ≤ a} (23/2) := by
  constructor
  · -- First, we'll prove that 23/2 is in the set.
    intro x y h
    have h23 : |2*x - 3*y + 3/2| + |y-1| + |2*y - x - 3| ≤ 23/2 := by
      cases' abs_cases (2*x - 3*y + 3/2) with h3 h3 <;> 
        cases' abs_cases (y - 1) with h4 h4 <;> 
          cases' abs_cases (2*y - x - 3) with h5 h5 <;> 
            cases' abs_cases x with h6 h6 <;> 
              cases' abs_cases y with h7 h7 <;> 
                all_goals 
                  try { 
                    linarith 
                  }
                  <;> try { 
                    nlinarith 
                  }
    linarith
  · -- Now we'll prove that 23/2 is the least such value.
    intro a ha
    have h21 := ha (0 : ℝ) (-1 : ℝ) (by norm_num [abs])
    norm_num [abs] at h21 ⊢
    all_goals linarith