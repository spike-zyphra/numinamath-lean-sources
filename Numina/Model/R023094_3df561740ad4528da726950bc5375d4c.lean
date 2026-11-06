import Mathlib

theorem inequalities_163525 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x * y ≤ z ∨ y * z ≤ x ∨ z * x ≤ y := by
  by_contra h
  push_neg at h
  have h1 : x * y > z := by linarith
  have h2 : y * z > x := by linarith
  have h3 : z * x > y := by linarith
  nlinarith [sq_nonneg (x * y * z - 1), sq_nonneg (x * y - z), sq_nonneg (y * z - x), sq_nonneg (z * x - y),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hxyz]