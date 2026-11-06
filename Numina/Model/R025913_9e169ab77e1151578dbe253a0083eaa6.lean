import Mathlib

theorem inequalities_598118 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    (27 / 4) * (x + y) * (y + z) * (z + x) ≥
    (Real.sqrt (x + y) + Real.sqrt (y + z) + Real.sqrt (z + x))^2 ∧
    (Real.sqrt (x + y) + Real.sqrt (y + z) + Real.sqrt (z + x))^2 ≥ 6 * Real.sqrt 3 := by
  have h1 : 0 < x + y := by linarith
  have h2 : 0 < y + z := by linarith
  have h3 : 0 < z + x := by linarith
  have h4 : Real.sqrt (x + y) ≥ 0 := by positivity
  have h5 : Real.sqrt (y + z) ≥ 0 := by positivity
  have h6 : Real.sqrt (z + x) ≥ 0 := by positivity
  have h7 : Real.sqrt (x + y) ^ 2 = x + y := by
    rw [Real.sq_sqrt]
    linarith
  have h8 : Real.sqrt (y + z) ^ 2 = y + z := by
    rw [Real.sq_sqrt]
    linarith
  have h9 : Real.sqrt (z + x) ^ 2 = z + x := by
    rw [Real.sq_sqrt]
    linarith
  constructor
  · -- First inequality
    nlinarith [sq_nonneg (Real.sqrt (x + y) - Real.sqrt (y + z)), sq_nonneg (Real.sqrt (y + z) - Real.sqrt (z + x)), sq_nonneg (Real.sqrt (z + x) - Real.sqrt (x + y)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + y by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + z by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z + x by positivity), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x)
        ]
  · -- Second inequality
    nlinarith [Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x), 
          h7, h8, h9, 
          sq_nonneg (Real.sqrt (x + y) - Real.sqrt (y + z)), sq_nonneg (Real.sqrt (y + z) - Real.sqrt (z + x)), sq_nonneg (Real.sqrt (z + x) - Real.sqrt (x + y)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
          Real.sqrt_nonneg (3 : ℝ), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]