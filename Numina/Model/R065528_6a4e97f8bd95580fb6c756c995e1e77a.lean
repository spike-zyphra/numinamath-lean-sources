import Mathlib

theorem algebra_1489 (x y z : ℝ) (h : Real.sqrt (x^2 - 2 * x * y + y^2) + 3 * x^2 + 6 * x * z + 2 * y + y^2 + 3 * z^2 + 1 = 0) :
    x + 3 * y - 2 * z = -6 ∧ 2 * x - y + z = 0 ∧ 2 * x - y + 3 * z = 2 := by

  have h1 : Real.sqrt (x^2 - 2 * x * y + y^2) = |x - y| := by
    have h2 : (x ^ 2 - 2 * x * y + y ^ 2) = (x - y) ^ 2 := by 
      ring
    rw [h2]
    rw [Real.sqrt_sq_eq_abs]

  rw [h1] at h

  have h_eq : |x - y| + 3 * (x + z) ^ 2 + (y + 1) ^ 2 = 0 := by 
    nlinarith

  have h5 : |x - y| = 0 := by 
    nlinarith [abs_nonneg (x - y), show 3 * (x + z) ^ 2 ≥ 0 by nlinarith, show (y + 1) ^ 2 ≥ 0 by nlinarith]

  have h6 : 3 * (x + z) ^ 2 = 0 := by 
    nlinarith [abs_nonneg (x - y), show 3 * (x + z) ^ 2 ≥ 0 by nlinarith, show (y + 1) ^ 2 ≥ 0 by nlinarith]

  have h7 : (y + 1) ^ 2 = 0 := by 
    nlinarith [abs_nonneg (x - y), show 3 * (x + z) ^ 2 ≥ 0 by nlinarith, show (y + 1) ^ 2 ≥ 0 by nlinarith]

  have h8 : x = y := by 
    rw [abs_eq_zero] at h5 
    linarith 
  have h9 : x + z = 0 := by 
    nlinarith [sq_nonneg (x + z)]
  have h10 : y + 1 = 0 := by 
    rw [sq_eq_zero_iff] at h7 
    linarith 
  have hx : x = -1 := by linarith [h8, h10]
  have hy : y = -1 := by linarith [h10]
  have hz : z = 1 := by linarith [h9, hx]

  constructor
  · -- Check first equation of C: x + 3y - 2z = -6
    rw [hx, hy, hz]
    norm_num
  constructor
  · -- Check second equation of C: 2x - y + z = 0
    rw [hx, hy, hz]
    norm_num
  · -- Check third equation of C: 2x - y + 3z = 2
    rw [hx, hy, hz]
    norm_num