import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_2884 :
  IsLeast {y : ℝ | ∃ x, y = 4 * abs (2 * x + 7) + 5 * abs (x - 1) + 2 * abs (x - 2) +
    3 * abs (x - 3) + 7 * abs (x - 4)} 65 := by
  constructor
  · -- First, we show that 65 is in the set
    use 1
    norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos]
  · -- Now, we show that 65 is the minimum
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : 4 * abs (2 * x + 7) + 5 * abs (x - 1) + 2 * abs (x - 2) + 3 * abs (x - 3) + 7 * abs (x - 4) ≥ 65 := by
      cases' abs_cases (2 * x + 7) with h1 h1 <;> 
        cases' abs_cases (x - 1) with h2 h2 <;> 
          cases' abs_cases (x - 2) with h3 h3 <;> 
            cases' abs_cases (x - 3) with h4 h4 <;> 
              cases' abs_cases (x - 4) with h5 h5 <;> 
                linarith 
    linarith [h1, hx]