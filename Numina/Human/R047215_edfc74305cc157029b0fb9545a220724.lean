import Mathlib
/-If x, y, z are positive real numbers, x + y + z = xyz, then $x(1-y^2)(1-z^2) + y(1-z^2)(1-x^2) + z(1-x^2)(1-y^2) ≥ 12√3$-/
theorem inequalities_600844 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x * (1 - y ^ 2) * (1 - z ^ 2) + y * (1 - z ^ 2) * (1 - x ^ 2) +
    z * (1 - x ^ 2) * (1 - y ^ 2) ≥ 12 * Real.sqrt 3 := by

  have h1 : x * (1 - y^2) * (1 - z^2) + y * (1 - z^2) * (1 - x^2) + z * (1 - x^2) * (1 - y^2) = 4 * (x * y * z) := by
    ring_nf
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
              h, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]

  have h2 : x * y * z ≥ 3 * Real.sqrt 3 := by
    have h3 : (x * y * z) ^ 2 ≥ 27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, h,
                Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

    have h4 : (3 * Real.sqrt 3) ^ 2 = 27 := by
      calc
        (3 * Real.sqrt 3) ^ 2 = 3^2 * (Real.sqrt 3)^2 := by ring
        _ = 9 * 3 := by norm_num
        _ = 27 := by norm_num

    nlinarith [h3, h4, Real.sqrt_nonneg 3]

  linarith [h1, h2, Real.sqrt_nonneg 3]
