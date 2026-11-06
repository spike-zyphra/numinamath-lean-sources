import Mathlib

theorem inequalities_168539 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by 
  have h1 : 0 ≤ x + 1 := by
    linarith [hx.1]
  have h2 : 0 ≤ 2 * x - 3 := by
    linarith [hx.1]
  have h3 : 0 ≤ 15 - 3 * x := by 
    linarith [hx.2]
  have h4 : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
  have h5 : Real.sqrt (2 * x - 3) ≥ 0 := Real.sqrt_nonneg (2 * x - 3)
  have h6 : Real.sqrt (15 - 3 * x) ≥ 0 := Real.sqrt_nonneg (15 - 3 * x)
  have h7 : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
  have h8 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < (2 * Real.sqrt 19) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.sqrt (x + 1) - Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), 
          Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), 
          Real.sqrt_nonneg (19), 
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), 
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), 
          mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)), 
          Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num), 
          mul_nonneg (show 0 ≤ (x : ℝ) by linarith [hx.1, hx.2]) (show 0 ≤ (5 - x : ℝ) by linarith [hx.1, hx.2])
        ]
  nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg 19, 
            sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x))
          ]