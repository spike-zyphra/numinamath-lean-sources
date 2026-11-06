import Mathlib

theorem algebra_8872 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 2) :
    x^2 * y^2 + y^2 * z^2 + z^2 * x^2 + x * y * z ≤ 1 := by 
  have h1 : z = 2 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (2 - x - y)), sq_nonneg (x - (2 - x - y)), 
      mul_nonneg hx hy, 
      mul_nonneg hy (show 0 ≤ 2 - x - y by nlinarith), 
      mul_nonneg (show 0 ≤ 2 - x - y by nlinarith) hx, 
      sq_nonneg (x + y - (2 - x - y)), 
      mul_nonneg (mul_nonneg hx hy) (show 0 ≤ (2 - x - y) by nlinarith)]