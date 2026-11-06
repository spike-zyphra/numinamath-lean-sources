import Mathlib

theorem inequalities_208362 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z)^2 / 3 ≥ x * √(y * z) + y * √(z * x) + z * √(x * y) := by 
  have h1 : x * √(y * z) + y * √(z * x) + z * √(x * y) ≤ x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) := by
    have h1 : √(y * z) ≤ (y + z) / 2 := by
      nlinarith [show (√(y * z)) ^ 2 = y * z by rw [Real.sq_sqrt]; positivity, sq_nonneg (y - z), mul_nonneg hy hz]
    have h2 : √(z * x) ≤ (z + x) / 2 := by
      nlinarith [show (√(z * x)) ^ 2 = z * x by rw [Real.sq_sqrt]; positivity, sq_nonneg (z - x), mul_nonneg hz hx]
    have h3 : √(x * y) ≤ (x + y) / 2 := by
      nlinarith [show (√(x * y)) ^ 2 = x * y by rw [Real.sq_sqrt]; positivity, sq_nonneg (x - y), mul_nonneg hx hy]
    nlinarith [h1, h2, h3, mul_nonneg hx (show 0 ≤ (√(y * z) : ℝ) by positivity), mul_nonneg hx (show 0 ≤ (√(z * x) : ℝ) by positivity), mul_nonneg hx (show 0 ≤ (√(x * y) : ℝ) by positivity)]
  have h4 : (x + y + z) ^ 2 / 3 ≥ x * y + y * z + z * x := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx]
  have h5 : x * √(y * z) + y * √(z * x) + z * √(x * y) ≤ x * y + y * z + z * x := by
    have h6 : x * √(y * z) + y * √(z * x) + z * √(x * y) ≤ x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) := h1
    have h7 : x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) = x * y + y * z + z * x := by 
      nlinarith
    linarith [h6, h7]
  linarith [h4, h5]