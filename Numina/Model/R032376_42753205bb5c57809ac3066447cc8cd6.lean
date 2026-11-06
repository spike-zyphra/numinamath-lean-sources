import Mathlib

open Real

theorem inequalities_603156 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    27 / 4 * (x + y) * (y + z) * (z + x) ≥
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ∧
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by 
  constructor
  · -- Prove the first inequality.
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (sqrt (x + y) - sqrt (y + z)), 
          sq_nonneg (sqrt (y + z) - sqrt (z + x)), 
          sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + y by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + z by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z + x by positivity), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
  · -- Prove the second inequality.
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (sqrt (x + y) - sqrt (y + z)), 
          sq_nonneg (sqrt (y + z) - sqrt (z + x)), 
          sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + y by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + z by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z + x by positivity), 
          sq_nonneg ((x + y + z) - sqrt 3), 
          Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          Real.sqrt_nonneg (x + y + z), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]