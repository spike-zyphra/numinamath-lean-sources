import Mathlib

theorem algebra_261167 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + 2 * y^2 = x + 2 * y + 3 * z) (h2 : y^2 + 2 * z^2 = 2 * x + 3 * y + 4 * z)
    (h3 : z^2 + 2 * x^2 = 3 * x + 4 * y + 5 * z) :
    (x, y, z) = (10 / 3, 5 / 3, 10 / 3) := by

  have h4 : (x - 10 / 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 10 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (z - 10 / 3),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h5 : (y - 5 / 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 10 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (z - 10 / 3),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h6 : (z - 10 / 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 10 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (z - 10 / 3),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have hx1 : x - 10 / 3 = 0 := by
    apply pow_eq_zero 
    exact h4

  have hx3 : x = 10 / 3 := by linarith

  have hy1 : y - 5 / 3 = 0 := by
    apply pow_eq_zero 
    exact h5

  have hy3 : y = 5 / 3 := by linarith

  have hz1 : z - 10 / 3 = 0 := by
    apply pow_eq_zero 
    exact h6

  have hz3 : z = 10 / 3 := by linarith

  simp [hx3, hy3, hz3]