import Mathlib

open Real
open scoped BigOperators

theorem inequalities_67057 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : x + y > z) (h' : y + z > x) (h'' : z + x > y) :
  |x^2 * (y - z) + y^2 * (z - x) + z^2 * (x - y)| < x * y * z := by

  have h1 : -x < y - z := by linarith
  have h2 : y - z < x := by linarith
  have h3 : -y < z - x := by linarith
  have h4 : z - x < y := by linarith
  have h5 : -z < x - y := by linarith
  have h6 : x - y < z := by linarith
  have h7 : -x * y * z < x^2 * (y - z) + y^2 * (z - x) + z^2 * (x - y) := by
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, h', h'', 
      mul_pos (show 0 < x + y - z by linarith) (show 0 < y + z - x by linarith), 
      mul_pos (show 0 < y + z - x by linarith) (show 0 < z + x - y by linarith), 
      mul_pos (show 0 < x + y - z by linarith) (show 0 < z + x - y by linarith)
      ]
  have h8 : x^2 * (y - z) + y^2 * (z - x) + z^2 * (x - y) < x * y * z := by
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, h', h'', 
      mul_pos (show 0 < x + y - z by linarith) (show 0 < y + z - x by linarith), 
      mul_pos (show 0 < y + z - x by linarith) (show 0 < z + x - y by linarith), 
      mul_pos (show 0 < x + y - z by linarith) (show 0 < z + x - y by linarith)
      ]
  have h9 : |x^2 * (y - z) + y^2 * (z - x) + z^2 * (x - y)| < x * y * z := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  exact h9