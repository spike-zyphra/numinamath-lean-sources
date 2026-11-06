import Mathlib

theorem algebra_604232 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y) * √((z + x) * (z + y)) + (y + z) * √((x + y) * (x + z)) + (z + x) * √((y + z) * (y + x)) ≥ 4 * (x * y + y * z + z * x):= by
  have h1 : 0 < z * x := by
    nlinarith
  have h2 : 0 < y * z := by
    nlinarith
  have h3 : 0 < x * y := by
    nlinarith
  have h4 : √((z + x) * (z + y)) = √(z + x) * √(z + y):= by
    rw [← Real.sqrt_mul (by positivity)]
  have h5 : √((x + y) * (x + z)) = √(x + y) * √(x + z):= by
    rw [← Real.sqrt_mul (by positivity)]
  have h6 : √((y + z) * (y + x)) = √(y + z) * √(y + x):= by
    rw [← Real.sqrt_mul (by positivity)]
  rw [h4] at *
  rw [h5] at *
  rw [h6] at *
  nlinarith [sq_nonneg (√(z + x) - √(z + y)), sq_nonneg (√(x + y) - √(x + z)), 
          sq_nonneg (√(y + z) - √(y + x)),
          Real.sqrt_nonneg (z + x), Real.sqrt_nonneg (z + y), 
          Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (x + z), 
          Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (y + x),
          mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (z + y)),
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (x + z)),
          mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (y + x)),
          Real.sq_sqrt (show (0 : ℝ) ≤ z + x by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z + y by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + y by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x + z by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + z by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y + x by positivity), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]