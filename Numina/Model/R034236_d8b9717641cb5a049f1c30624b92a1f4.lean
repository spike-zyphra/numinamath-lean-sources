import Mathlib

theorem algebra_138404 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 3) (h2 : y^2 + z^2 + y * z = 4) (h3 : z^2 + x^2 + z * x = 7) :
    x + y + z = Real.sqrt 13 := by

  have h4 : (x + y + z) ^ 2 = 13 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  
  have h5 : x + y + z ≥ 0 := by
    linarith [show x ≥ 0 by linarith, show y ≥ 0 by linarith, show z ≥ 0 by linarith]

  have h6 : x + y + z = Real.sqrt 13 := by
    have h7 : Real.sqrt ((x + y + z) ^ 2) = Real.sqrt (13) := by
      rw [h4]
    have h8 : Real.sqrt ((x + y + z) ^ 2) = x + y + z := by
      rw [Real.sqrt_sq (show 0 ≤ x + y + z by linarith)]
    rw [h8] at h7
    linarith [Real.sqrt_nonneg 13]
  
  exact h6