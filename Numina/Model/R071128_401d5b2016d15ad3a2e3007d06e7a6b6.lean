import Mathlib

theorem algebra_322615 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + (1 / 3) * y^2 = 25) (h2 : z^2 + (1 / 3) * y^2 = 9)
    (h3 : x^2 + x * z + z^2 = 16) :
    x * y + 2 * y * z + 3 * x * z = 24 * Real.sqrt 3 := by
  have h4 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - y / 2 - z * Real.sqrt 3 / 2), sq_nonneg (z - Real.sqrt 3 * x / 2), sq_nonneg (y - Real.sqrt 3 * x), h1, h2, h3, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : (x * y + 2 * y * z + 3 * x * z) = 24 * Real.sqrt 3 := by
    have h10 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = 1728 := h4
    have h11 : (24 * Real.sqrt 3 : ℝ) ^ 2 = 1728 := by
      calc
        (24 * Real.sqrt 3 : ℝ) ^ 2 = (24 : ℝ) ^ 2 * (Real.sqrt 3 : ℝ) ^ 2 := by ring
        _ = (24 : ℝ) ^ 2 * (3 : ℝ) := by
          rw [Real.sq_sqrt]; all_goals linarith
        _ = (24 * 24) * (3 : ℝ) := by ring
        _ = (24 * (24 * 3) : ℝ) := by ring
        _ = (1728 : ℝ) := by
          norm_num
    have h13 : (x * y + 2 * y * z + 3 * x * z) = (24 * Real.sqrt 3 : ℝ) := by
      have h14 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = (24 * Real.sqrt 3 : ℝ) ^ 2 := by
        linarith [h10, h11]
      have h15 : 0 ≤ (x * y + 2 * y * z + 3 * x * z : ℝ) := by
        nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      have h16 : 0 ≤ (24 * Real.sqrt 3 : ℝ) := by
        positivity
      nlinarith [h14, h15, h16, Real.sqrt_nonneg 3, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
    linarith
  rw [h5]
  <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (x * y + 2 * y * z + 3 * x * z), Real.sqrt_nonneg (x * y + 2 * y * z + 3 * x * z), Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
  <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 3, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]