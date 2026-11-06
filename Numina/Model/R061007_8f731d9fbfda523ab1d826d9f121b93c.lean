import Mathlib

open Real
open scoped BigOperators

theorem inequalities_195383 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
  (h : x + y + z = 1) :
  x^2 + y^2 + z^2 ≥ x^3 + y^3 + z^3 + 6 * x * y * z := by

  have h1 : z = 1 - x - y := by linarith

  rw [h1]

  nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
          mul_pos hx hy, mul_pos hx (show (1 - x - y) > 0 by nlinarith), mul_pos hy (show (1 - x - y) > 0 by nlinarith)]