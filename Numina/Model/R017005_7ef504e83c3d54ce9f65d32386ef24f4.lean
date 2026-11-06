import Mathlib

open Real

theorem algebra_5578 {x : ℝ} (hx : x = sqrt (110 + sqrt (110 + sqrt (110 + x)))) : x = 11 := by
  have h3 : x ≥ 0 := by 
    rw [hx]
    positivity

  have h9 : x ≤ 11 := by
    nlinarith [sq_nonneg (x - 11), sq_nonneg (sqrt (110 + sqrt (110 + x)) - 11), sq_nonneg (sqrt (110 + x) - 11), 
      Real.sqrt_nonneg (110 + sqrt (110 + x)), Real.sqrt_nonneg (110 + x), Real.sqrt_nonneg (110 + sqrt (110 + sqrt (110 + x))), 
      Real.sq_sqrt (show 0 ≤ (110 + sqrt (110 + sqrt (110 + x)) : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (110 + sqrt (110 + x) : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (110 + x : ℝ) by nlinarith [h3]
      )
    ]

  -- Prove x ≥ 11.
  have h10 : x ≥ 11 := by
    nlinarith [sq_nonneg (x - 11), sq_nonneg (sqrt (110 + sqrt (110 + x)) - 11), sq_nonneg (sqrt (110 + x) - 11), 
      Real.sqrt_nonneg (110 + sqrt (110 + x)), Real.sqrt_nonneg (110 + x), Real.sqrt_nonneg (110 + sqrt (110 + sqrt (110 + x))), 
      Real.sq_sqrt (show 0 ≤ (110 + sqrt (110 + sqrt (110 + x)) : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (110 + sqrt (110 + x) : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (110 + x : ℝ) by nlinarith [h3]
      )
    ]

  -- Therefore x = 11.
  linarith