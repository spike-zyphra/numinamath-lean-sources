import Mathlib

open Real

theorem inequalities_41312 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    27 / 4 * (x + y) * (y + z) * (z + x) ≥
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ∧
    (sqrt (x + y) + sqrt (y + z) + sqrt (z + x))^2 ≥ 6 * sqrt 3 := by
  constructor
  · -- Prove the first inequality: $\frac{27}{4} (x+y)(y+z)(z+x) \geq (sqrt(x+y) + ...)^2$
    nlinarith [sq_nonneg (√(x + y) - √(y + z)), sq_nonneg (√(y + z) - √(z + x)), sq_nonneg (√(z + x) - √(x + y)), 
        Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
        mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
        mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
        mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ y + z by linarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ z + x by linarith), 
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
      ]
  · -- Prove the second inequality: $(\sqrt(x+y) + ...)^2 \geq 6 \sqrt 3$
    have h2 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 ≥ 6 * sqrt 3 := by
      nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), 
          sq_nonneg (sqrt (y + z) - sqrt (z + x)), 
          sq_nonneg (sqrt (z + x) - sqrt (x + y)), 
          Real.sqrt_nonneg (x + y), 
          Real.sqrt_nonneg (y + z), 
          Real.sqrt_nonneg (z + x), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          sq_nonneg ((sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ^ 2 - 6 * sqrt 3), 
          sq_nonneg ((sqrt (x + y) ^ 2 + sqrt (y + z) ^ 2 + sqrt (z + x) ^ 2) - (x + y + z)), 
          Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + y) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (y + z) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (z + x) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + y : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (y + z : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (z + x : ℝ) by linarith), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          sq_nonneg (x + y + z - Real.sqrt 3) 
        ]
    exact h2