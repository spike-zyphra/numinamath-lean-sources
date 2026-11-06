import Mathlib

open Real

theorem inequalities_597893 (x : ℝ) :
    |sqrt (x^2 + x + 1) - sqrt (x^2 - x + 1)| < 1 := by
  have h1 : 0 ≤ x ^ 2 + x + 1 := by 
    nlinarith [sq_nonneg (x + 1 / 2)]
  have h2 : 0 ≤ x ^ 2 - x + 1 := by 
    nlinarith [sq_nonneg (x - 1 / 2)]
  have h3 : sqrt (x^2 + x + 1) ≥ 0 := Real.sqrt_nonneg (x^2 + x + 1)
  have h4 : sqrt (x^2 - x + 1) ≥ 0 := Real.sqrt_nonneg (x^2 - x + 1)
  have h5 : -1 < sqrt (x^2 + x + 1) - sqrt (x^2 - x + 1) := by
    nlinarith [Real.sqrt_nonneg (x^2 + x + 1), Real.sqrt_nonneg (x^2 - x + 1), 
      Real.sq_sqrt h1, Real.sq_sqrt h2, 
        sq_nonneg (sqrt (x ^ 2 + x + 1) - sqrt (x ^ 2 - x + 1) + 1), 
          sq_nonneg (sqrt (x ^ 2 + x + 1) - 1), 
            mul_nonneg (Real.sqrt_nonneg (x^2 + x + 1)) (Real.sqrt_nonneg (x^2 - x + 1))
    ]
  have h7 : sqrt (x^2 + x + 1) - sqrt (x^2 - x + 1) < 1 := by
    nlinarith [Real.sqrt_nonneg (x^2 + x + 1), Real.sqrt_nonneg (x^2 - x + 1), 
      Real.sq_sqrt h1, Real.sq_sqrt h2, 
        sq_nonneg (sqrt (x ^ 2 + x + 1) - sqrt (x ^ 2 - x + 1) - 1), 
          sq_nonneg (sqrt (x ^ 2 - x + 1) - 1), 
            mul_nonneg (Real.sqrt_nonneg (x^2 + x + 1)) (Real.sqrt_nonneg (x^2 - x + 1))
    ]
  rw [abs_lt]
  constructor <;> linarith [h5, h7]