import Mathlib

theorem algebra_309773 {x : ℝ} (hx : (6 * x + 5) * (1 + Real.sqrt ((6 * x + 5) ^ 2 + 4)) +
    x * (1 + Real.sqrt (x ^ 2 + 4)) = 0) :
    x = -5 / 7 := by

  have h1 : (6 * x + 5) * (1 + Real.sqrt ((6 * x + 5) ^ 2 + 4)) + x * (1 + Real.sqrt (x ^ 2 + 4)) = 0 := by linarith
  have h4 : x = -5 / 7 := by
    nlinarith [Real.sqrt_nonneg ((6 * x + 5) ^ 2 + 4), Real.sqrt_nonneg (x ^ 2 + 4), 
      sq_nonneg (Real.sqrt ((6 * x + 5) ^ 2 + 4) - Real.sqrt (x ^ 2 + 4)), 
      sq_nonneg (6 * x + 5 + x), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 * x + 5) ^ 2 + 4 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (x) ^ 2 + 4 by nlinarith), 
      mul_nonneg (Real.sqrt_nonneg ((6 * x + 5) ^ 2 + 4)) (Real.sqrt_nonneg (x ^ 2 + 4)), 
      sq_nonneg ((6 * x + 5) + x)
    ]
  exact h4