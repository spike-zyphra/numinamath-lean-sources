import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_145020 (x y : ℝ) (h : x^2/3 + y^2 = 1) :
    2 ≤ abs (2*x + y - 4) + abs (4 - x - 2*y) ∧
    abs (2*x + y - 4) + abs (4 - x - 2*y) ≤ 14 := by

  constructor
  · -- Prove that $2 \leq |2x + y - 4| + |4 - x - 2y|$
    cases' abs_cases (2 * x + y - 4) with h1 h1 <;> 
      cases' abs_cases (4 - x - 2 * y) with h2 h2 <;> 
        try { 
          nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y - 1 / 2), 
            sq_nonneg (2 * x + y - 4), sq_nonneg (4 - x - 2 * y), 
              mul_self_nonneg (x + 3 / 2), mul_self_nonneg (x - 3 / 2), 
                mul_self_nonneg (y - 1 / 2), mul_self_nonneg (y + 1 / 2)
                  ]
        }
  · -- Prove that $|2x + y - 4| + |4 - x - 2y| \leq 14$
    cases' abs_cases (2 * x + y - 4) with h1 h1 <;> 
      cases' abs_cases (4 - x - 2 * y) with h2 h2 <;> 
        try { 
          nlinarith [sq_nonneg (x - 3 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x + 3 / 2), sq_nonneg (y - 1 / 2), 
            sq_nonneg (2 * x + y - 4), sq_nonneg (4 - x - 2 * y), 
              mul_self_nonneg (x + 3 / 2), mul_self_nonneg (x - 3 / 2), 
                mul_self_nonneg (y - 1 / 2), mul_self_nonneg (y + 1 / 2)
                  ]
        }