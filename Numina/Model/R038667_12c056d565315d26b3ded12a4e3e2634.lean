import Mathlib

open Real

theorem inequalities_600652 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    27 / 4 * (x + y) * (y + z) * (z + x) ≥ (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ∧
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by

  have h1 : 0 < x + y := by linarith
  have h2 : 0 < y + z := by linarith
  have h3 : 0 < z + x := by linarith

  constructor
  · -- Prove 27/4 * (x + y) * (y + z) * (z + x) ≥ (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2
    nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
      Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ y + z by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ z + x by linarith),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
      mul_pos hx (show 0 < x * y from by nlinarith), 
      mul_pos hy (show 0 < y * z from by nlinarith), 
      mul_pos hz (show 0 < z * x from by nlinarith)
    ]
  · -- Prove (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3
    have h5 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 ≥ 6 * sqrt 3 := by
      nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + z by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z + x by linarith),
          sq_nonneg (sqrt (x + y) ^ 2 - sqrt (y + z) ^ 2 ), sq_nonneg (sqrt (y + z) ^ 2 - sqrt (z + x) ^ 2 ), 
          sq_nonneg (sqrt (z + x) ^ 2 - sqrt (x + y) ^ 2 ), 
          Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x)
        ]
    linarith [h5]