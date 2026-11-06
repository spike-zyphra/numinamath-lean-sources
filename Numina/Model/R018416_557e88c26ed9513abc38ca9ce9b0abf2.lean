import Mathlib

open Real

theorem inequalities_597344 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x ≥
    2 * (sqrt x + sqrt y + sqrt z) := by
  have h1 : 0 < sqrt x := by positivity
  have h2 : 0 < sqrt y := by positivity
  have h3 : 0 < sqrt z := by positivity
  have h4 : sqrt x ^ 2 = x := by rw [Real.sq_sqrt]; linarith
  have h5 : sqrt y ^ 2 = y := by rw [Real.sq_sqrt]; linarith
  have h6 : sqrt z ^ 2 = z := by rw [Real.sq_sqrt]; linarith
  have h7 : sqrt x * sqrt y * sqrt z = 1 := by
    have h8 : sqrt x * sqrt y * sqrt z = sqrt (x * y * z) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [h8, hxyz, Real.sqrt_one]
  nlinarith [sq_nonneg (sqrt x ^ 2 - 1), sq_nonneg (sqrt y ^ 2 - 1), sq_nonneg (sqrt z ^ 2 - 1),
          sq_nonneg (sqrt x - 1), sq_nonneg (sqrt y - 1), sq_nonneg (sqrt z - 1),
          sq_nonneg (sqrt x ^ 2 + sqrt y ^ 2 + sqrt z ^ 2 - sqrt x * sqrt y - sqrt y * sqrt z - sqrt z * sqrt x),
          sq_nonneg (sqrt x - sqrt y), sq_nonneg (sqrt y - sqrt z), sq_nonneg (sqrt z - sqrt x),
          Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z,
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y),
          mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z),
          mul_nonneg (Real.sqrt_nonneg z) (Real.sqrt_nonneg x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]