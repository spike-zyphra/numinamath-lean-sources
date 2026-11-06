import Mathlib

theorem algebra_133399 (x : ℝ) : abs (abs (abs (abs (x^2 - x - 1) - 2) - 3) - 4) - 5 = x^2 + x - 30 ↔
    x = 7.5 := by
  constructor
  · -- Assume the equation holds, prove x = 7.5
    intro h_eq
    have h_eq1 : abs (abs (abs (abs (x ^ 2 - x - 1) - 2) - 3) - 4) = x ^ 2 + x - 25 := by
      linarith
    have h_eq2 : x = 7.5 := by
      cases' abs_cases (abs (abs (abs (x ^ 2 - x - 1) - 2) - 3) - 4) with h2 h2 <;> 
          cases' abs_cases (abs (abs (x ^ 2 - x - 1) - 2) - 3) with h3 h3 <;> 
              cases' abs_cases (abs (x ^ 2 - x - 1) - 2) with h4 h4 <;> 
                cases' abs_cases (x ^ 2 - x - 1) with h5 h5 <;> 
                    nlinarith
    linarith
  · -- Assume x = 7.5 prove the equation
    intro h_eq
    rw [h_eq]
    norm_num [abs_of_nonneg, abs_of_neg]