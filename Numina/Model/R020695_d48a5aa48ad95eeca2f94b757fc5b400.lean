import Mathlib

theorem algebra_159640 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + y^2 + x * y = 1) (h2 : y^2 + z^2 + y * z = 4) (h3 : z^2 + x^2 + z * x = 5) :
    x + y + z = Real.sqrt (5 + 2 * Real.sqrt 3) := by
  have h4 : (x + y + z)^2 = 5 + 2 * Real.sqrt 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  have h5 : x + y + z ≥ 0 := by positivity
  have h6 : x + y + z = Real.sqrt (5 + 2 * Real.sqrt 3) := by
    have h7 : (x + y + z) ^ 2 = 5 + 2 * Real.sqrt 3 := h4
    have h8 : x + y + z ≥ 0 := h5
    have h9 : Real.sqrt ((x + y + z) ^ 2) = Real.sqrt (5 + 2 * Real.sqrt 3) := by
      rw [h7]
    have h10 : Real.sqrt ((x + y + z) ^ 2) = x + y + z := by
      rw [Real.sqrt_sq (show 0 ≤ x + y + z by linarith)]
    rw [h10] at h9
    linarith
  exact h6