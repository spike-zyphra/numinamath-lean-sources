import Mathlib

open Real

theorem inequalities_86932 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 2 / 3 ≥ x * sqrt (y * z) + y * sqrt (z * x) + z * sqrt (x * y) := by

  have h1 : sqrt (y * z) ≤ (y + z) / 2 := by
    nlinarith [sq_nonneg (sqrt (y * z) ), sq_nonneg ((y + z) / 2), 
              Real.sqrt_nonneg (y * z), mul_nonneg hy hz, 
              Real.sq_sqrt (mul_nonneg hy hz),
              sq_nonneg (sqrt (y * z) - (y + z) / 2), 
              sq_nonneg (y - z)]

  have h2 : sqrt (z * x) ≤ (z + x) / 2 := by
    nlinarith [sq_nonneg (sqrt (z * x) ), sq_nonneg ((z + x) / 2),
              Real.sqrt_nonneg (z * x), mul_nonneg hz hx, 
              Real.sq_sqrt (mul_nonneg hz hx), 
              sq_nonneg (sqrt (z * x) - (z + x) / 2), 
              sq_nonneg (z - x)]

  have h3 : sqrt (x * y) ≤ (x + y) / 2 := by
    nlinarith [sq_nonneg (sqrt (x * y) ), sq_nonneg ((x + y) / 2), 
              Real.sqrt_nonneg (x * y), mul_nonneg hx hy, 
              Real.sq_sqrt (mul_nonneg hx hy), 
              sq_nonneg (sqrt (x * y) - (x + y) / 2), 
              sq_nonneg (x - y)]

  have h4 : x * sqrt (y * z) ≤ x * ((y + z) / 2) := by
    have hx' : 0 ≤ x := by linarith
    nlinarith [h1, hx']

  have h5 : y * sqrt (z * x) ≤ y * ((z + x) / 2) := by
    have hy' : 0 ≤ y := by linarith
    nlinarith [h2, hy']

  have h6 : z * sqrt (x * y) ≤ z * ((x + y) / 2) := by
    have hz' : 0 ≤ z := by linarith
    nlinarith [h3, hz']

  have h7 : x * sqrt (y * z) + y * sqrt (z * x) + z * sqrt (x * y) ≤ x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) := by
    linarith [h4, h5, h6]

  have h8 : x * ((y + z) / 2) + y * ((z + x) / 2) + z * ((x + y) / 2) = (x * y + y * z + z * x) := by
    ring

  have h9 : (x + y + z) ^ 2 / 3 ≥ x * y + y * z + z * x := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

  linarith [h7, h8, h9]