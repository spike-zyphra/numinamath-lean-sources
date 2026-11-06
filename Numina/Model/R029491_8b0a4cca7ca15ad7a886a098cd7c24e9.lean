import Mathlib

open Real

theorem algebra_318057 (a b : ℝ) (ha : a^2 ≤ 2) (hb : b^2 ≤ 2) :
    a * sqrt (2 - b^2) + b * sqrt (2 - a^2) ≤ 2 := by

  have h1 : 0 ≤ 2 - b ^ 2 := by nlinarith
  have h2 : 0 ≤ 2 - a ^ 2 := by nlinarith
  have h3 : (a * sqrt (2 - b ^ 2) + b * sqrt (2 - a ^ 2)) ^ 2 ≤ (a ^ 2 + b ^ 2) * ((2 - b ^ 2) + (2 - a ^ 2)) := by
    nlinarith [ sq_nonneg (a * sqrt (2 - a ^ 2) - b * sqrt (2 - b ^ 2)), sq_nonneg (a * sqrt (2 - a ^ 2) - b * sqrt (2 - b ^ 2)), sq_nonneg (a - b), sq_nonneg (sqrt (2 - a^2) - sqrt (2 - b^2)), Real.sqrt_nonneg (2 - a^2), Real.sqrt_nonneg (2 - b^2), 
      Real.sq_sqrt (show 0 ≤ (2 - a^2 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (2 - b^2 : ℝ) by nlinarith),
      mul_nonneg (Real.sqrt_nonneg (2 - a^2)) (Real.sqrt_nonneg (2 - b^2)), 
      sq_nonneg (sqrt (2 - a^2) * b - sqrt (2 - b^2) * a)
    ]
  have h4 : (a ^ 2 + b ^ 2) * ((2 - b ^ 2) + (2 - a ^ 2)) ≤ 4 := by
    nlinarith [ sq_nonneg (a^2 + b^2 - 2), sq_nonneg (a - b), sq_nonneg (a + b), Real.sqrt_nonneg (2 - a^2), Real.sqrt_nonneg (2 - b^2)
    ]
  have h5 : (a * sqrt (2 - b ^ 2) + b * sqrt (2 - a ^ 2)) ^ 2 ≤ 4 := by
    nlinarith [ h3, h4 ]
  have h6 : a * sqrt (2 - b ^ 2) + b * sqrt (2 - a ^ 2) ≤ 2 := by
    nlinarith [ show (a * sqrt (2 - b^2) + b * sqrt (2 - a^2)) ^ 2 ≤ 4 by linarith, sq_nonneg (a * sqrt (2 - b^2) + b * sqrt (2 - a^2) - 2) ]
  exact h6