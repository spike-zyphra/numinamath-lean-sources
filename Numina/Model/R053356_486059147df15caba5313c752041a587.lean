import Mathlib

theorem algebra_198606 (a b c : ℝ) :
    ∃ x, (x - a) * (x - b) - c^2 = 0 := by 
  use (a + b + Real.sqrt ( (a - b)^2 + 4 * c^2 )) / 2
  have h : ( ( (a + b + Real.sqrt ( (a - b)^2 + 4 * c^2 )) / 2 ) - a ) * ( ( (a + b + Real.sqrt ( (a - b)^2 + 4 * c^2 )) / 2 ) - b ) - c^2 = 0 := by
    nlinarith [Real.sqrt_nonneg ((a - b) ^ 2 + 4 * c ^ 2), Real.sq_sqrt (show 0 ≤ (a - b) ^ 2 + 4 * c ^ 2 by positivity)]
  linarith