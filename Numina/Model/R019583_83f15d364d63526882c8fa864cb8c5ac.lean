import Mathlib

theorem algebra_322697
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25)
    (h2 : y^2 / 3 + z^2 = 9)
    (h3 : z^2 + x * z + x^2 = 16) :
    x * y + 2 * y * z + 3 * x * z = 24 * Real.sqrt 3 := by 
  have h4 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - z), sq_nonneg (y - z * Real.sqrt 3), sq_nonneg (x - y * Real.sqrt 3 / 2), sq_nonneg (y ^ 2 - 27), sq_nonneg (z ^ 2 - 9), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    ]
  have h5 : 0 ≤ x * y + 2 * y * z + 3 * x * z := by
    positivity
  have h6 : x * y + 2 * y * z + 3 * x * z = Real.sqrt 1728 := by
    have h7 : (x * y + 2 * y * z + 3 * x * z) ≥ 0 := by
      positivity
    have h8 : (Real.sqrt 1728) ^ 2 = 1728 := Real.sq_sqrt (by norm_num)
    have h9 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = (Real.sqrt 1728) ^ 2 := by
      rw [h8]
      linarith [h4]
    have h10 : (x * y + 2 * y * z + 3 * x * z) = Real.sqrt 1728 := by
      nlinarith [Real.sqrt_nonneg 1728, h7]
    linarith
  -- Now express sqrt(1728) as 24 * sqrt(3)
  have h7 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
  rw [h6, h7]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]