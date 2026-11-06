import Mathlib

theorem algebra_313531 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 3) (h2 : y^2 + z^2 + y * z = 4) (h3 : z^2 + x^2 + z * x = 7) :
    x + y + z = Real.sqrt 13 := by
  have h4 : (x + y + z) ^ 2 = 13 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  have h5 : x + y + z > 0 := by
    nlinarith [hx, hy, hz]
  have h6 : x + y + z = Real.sqrt 13 := by
    have h7 : (x + y + z) ^ 2 = 13 := h4
    have h8 : x + y + z ≥ 0 := by linarith
    have h9 : Real.sqrt 13 ≥ 0 := Real.sqrt_nonneg 13
    have h6 : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    have h10 : (x + y + z) ^ 2 = (Real.sqrt 13) ^ 2 := by linarith
    have h11 : x + y + z = Real.sqrt 13 := by
      nlinarith [h10, h8, h9]
    exact h11
  exact h6