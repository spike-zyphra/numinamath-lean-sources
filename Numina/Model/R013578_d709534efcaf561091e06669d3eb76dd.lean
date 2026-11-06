import Mathlib

open Real

theorem inequalities_312007 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    27 / 4 * (x + y) * (y + z) * (z + x) ≥
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ∧
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by
  constructor
  · -- Prove the first inequality
    nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)),
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
      Real.sq_sqrt (show 0 ≤ x + y by linarith),
      Real.sq_sqrt (show 0 ≤ y + z by linarith),
      Real.sq_sqrt (show 0 ≤ z + x by linarith),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  · -- Prove the second inequality
    have h8 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by
      have h9 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 - 6 * sqrt 3 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
          sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
          Real.sq_sqrt (show 0 ≤ (x + y) by linarith), 
          Real.sq_sqrt (show 0 ≤ (y + z) by linarith), 
          Real.sq_sqrt (show 0 ≤ (z + x) by linarith), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          sq_nonneg ( (sqrt (x + y) ) ^ 2 - (sqrt (y + z) ) ^ 2 ), 
          sq_nonneg ( (sqrt (y + z) ) ^ 2 - (sqrt (z + x) ) ^ 2 ), 
          sq_nonneg ( (sqrt (z + x) ) ^ 2 - (sqrt (x + y) ) ^ 2 ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (y + z : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (z + x : ℝ) by linarith ), 
          mul_nonneg (Real.sqrt_nonneg (x + y) ) (Real.sqrt_nonneg (y + z) ), 
          mul_nonneg (Real.sqrt_nonneg (y + z) ) (Real.sqrt_nonneg (z + x) ), 
          mul_nonneg (Real.sqrt_nonneg (z + x) ) (Real.sqrt_nonneg (x + y) ), 
          sq_nonneg (sqrt (x + y) - sqrt (y + z) ), sq_nonneg (sqrt (y + z) - sqrt (z + x) ), sq_nonneg (sqrt (z + x) - sqrt (x + y) )
          ]
      linarith
    linarith