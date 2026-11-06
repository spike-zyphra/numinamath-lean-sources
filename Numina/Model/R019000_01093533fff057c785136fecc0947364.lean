import Mathlib

open Real

theorem inequalities_597679 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  have h1 : 3 / 2 ≤ x := hx.1
  have h2 : x ≤ 5 := hx.2
  have h3 : 0 ≤ 2 * x - 3 := by
    linarith
  have h4 : 0 ≤ 15 - 3 * x := by
    nlinarith
  have h5 : (2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (2 * sqrt 19) ^ 2 := by
    nlinarith [sq_nonneg (2 * sqrt (x + 1) - sqrt (2 * x - 3) - sqrt (15 - 3 * x)), 
          sq_nonneg (sqrt (2 * x - 3) - sqrt (15 - 3 * x)), 
          sq_nonneg (sqrt (x + 1) - sqrt ((2 * x - 3))), 
          sq_nonneg (sqrt (x + 1) - sqrt ((15 - 3 * x))), 
          Real.sqrt_nonneg (x + 1), 
          Real.sqrt_nonneg (2 * x - 3), 
          Real.sqrt_nonneg (15 - 3 * x), 
          Real.sqrt_nonneg (19),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)),
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)),
          mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)),
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1) by linarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3) by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x) by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)
          ]
  have h6 : 2 * sqrt (x + 1) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
    nlinarith [h5, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg (19)]
  exact h6