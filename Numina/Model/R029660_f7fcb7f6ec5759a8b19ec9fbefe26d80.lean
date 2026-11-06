import Mathlib

theorem algebra_316830 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 1) (h2 : y^2 + z^2 + y * z = 2) (h3 : z^2 + x^2 + z * x = 3) :
    x + y + z = Real.sqrt (3 + Real.sqrt 6) := by
  have h4 : (x + y + z) ^ 2 = 3 + Real.sqrt 6 := by
    have h5 : (x + y + z) ^ 2 = 3 + Real.sqrt 6 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
    linarith
  have h5 : x + y + z ≥ 0 := by
    linarith [hx, hy, hz]
  have h6 : x + y + z = Real.sqrt (3 + Real.sqrt 6) := by
    have h6 : (x + y + z) ^ 2 = 3 + Real.sqrt 6 := h4
    have h7 : x + y + z ≥ 0 := h5
    have h8 : Real.sqrt ((x + y + z) ^ 2) = Real.sqrt (3 + Real.sqrt 6) := by
      rw [h6]
    have h9 : Real.sqrt ((x + y + z) ^ 2) = x + y + z := by
      rw [Real.sqrt_sq]
      linarith
    linarith [h9, h8]
  exact h6