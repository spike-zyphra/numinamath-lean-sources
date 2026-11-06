import Mathlib

theorem inequalities_45117 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ 2) (hyz : y ≤ 3) (hsum : x + y + z = 11) :
    x * y * z ≤ 36 := by
  have hz' : z = 11 - x - y := by linarith
  rw [hz']
  have h1 : x ≤ 2 := by linarith
  have h2 : y ≤ 3 := by linarith
  have h3 : 11 - x - y ≥ 6 := by
    nlinarith
  have h4 : x * y ≤ 6 := by
    nlinarith [mul_pos hx hy, h1, h2]
  nlinarith [mul_pos hx hy, mul_pos hx (show (0 : ℝ) < 11 - x - y by nlinarith), mul_pos hy (show (0 : ℝ) < 11 - x - y by nlinarith), 
      h1, h2, h3, sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg ((11 - x - y) - 6)]