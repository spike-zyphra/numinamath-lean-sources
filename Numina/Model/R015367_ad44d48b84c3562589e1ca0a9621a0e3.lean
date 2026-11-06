import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_243470 (P : ℝ × ℝ) (hP : P.1^2/8 - P.2^2/4 = 1) :
    abs (P.1 - P.2) ≥ 2 := by 
  have h1 : (P.1 - P.2) ^ 2 ≥ 4 := by 
    nlinarith [sq_nonneg (P.1 - 2 * P.2), sq_nonneg (P.1 + 2 * P.2), 
          sq_nonneg (P.1 - 4), sq_nonneg (P.2 - 2), 
          sq_nonneg (P.1 + 4), sq_nonneg (P.2 + 2)
    ]
  have h2 : abs (P.1 - P.2) ≥ 2 := by 
    cases' abs_cases (P.1 - P.2) with h3 h3 
    · -- Case where |P.1 - P.2| = P.1 - P.2.
      nlinarith 
    · -- Case where |P.1 - P.2| = -(P.1 - P.2).
      nlinarith 
  exact h2