import Mathlib

theorem inequalities_139797 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    x^2 * y^2 + y^2 * z^2 + z^2 * x^2 + x^2 * y^2 * z^2 ≤ 1 / 16 := by 
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x + y - 1/2), sq_nonneg (y + x - 1/2), sq_nonneg (y + (1 - x - y) - 1/2), sq_nonneg (x + (1 - x - y) - 1/2), 
          mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) hx, 
          mul_nonneg (mul_nonneg hx hy) (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ x * y by nlinarith) (show 0 ≤ (1 - x - y) ^ 2 by nlinarith) 
  ]