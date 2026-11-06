import Mathlib

open Real

theorem inequalities_57078 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x ≥
    2 * (sqrt x + sqrt y + sqrt z) := by
  have h1 : x + y * z ≥ 2 := by
    have h2 : x * (y * z) = 1 := by
      have h2' : x * y * z = 1 := hxyz
      nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y * z - 1), mul_pos hx (show 0 < y * z by nlinarith [show 0 < y by linarith, show 0 < z by linarith]), (show 0 < y by linarith), (show 0 < z by linarith), mul_pos (show 0 < y by linarith) (show 0 < z by linarith)]
  have h2 : y + x * z ≥ 2 := by
    have h3 : y * (x * z) = 1 := by
      have hxyz' : x * y * z = 1 := hxyz
      nlinarith
    nlinarith [sq_nonneg (y - 1), sq_nonneg (x * z - 1), mul_pos (show 0 < y by linarith) (show 0 < x * z by nlinarith [show 0 < x by linarith, show 0 < z by linarith]), (show 0 < x by linarith), (show 0 < z by linarith), mul_pos (show 0 < x by linarith) (show 0 < z by linarith)]
  have h3 : z + x * y ≥ 2 := by
    have h4 : z * (x * y) = 1 := by
      have hxyz' : x * y * z = 1 := hxyz
      nlinarith
    nlinarith [sq_nonneg (z - 1), sq_nonneg (x * y - 1), mul_pos (show 0 < z by linarith) (show 0 < x * y by nlinarith [show 0 < x by linarith, show 0 < y by linarith]), (show 0 < x by linarith), (show 0 < y by linarith), mul_pos (show 0 < x by linarith) (show 0 < y by linarith)]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (sqrt x - 1), sq_nonneg (sqrt y - 1), sq_nonneg (sqrt z - 1),
          Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z,
          Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (z : ℝ) by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ z by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ z by linarith)
      ]