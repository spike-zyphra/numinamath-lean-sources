import Mathlib

open Real Set

theorem inequalities_600367 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 3) :
    x^4 + 2 * y^4 + 3 * z^4 ≥ (3 * (3 / 2)^3)^4 / ((3 / 2)^4 + 2 * (3 / 2)^4 + 3 * (3 / 2)^4)^3 := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : x^4 + 2 * y^4 + 3 * z^4 ≥ 3 / 8 := by
    have h3 : z = 3 - x - y := by linarith
    rw [h3]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (3 - x - y)), sq_nonneg (y - (3 - x - y)), 
      sq_nonneg (x + y - (3 - x - y)), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - (3 - x - y)^2), sq_nonneg (y^2 - (3 - x - y)^2), 
      mul_pos hx hy, mul_pos hx (show 0 < 3 - x - y by nlinarith), mul_pos hy (show 0 < 3 - x - y by nlinarith), 
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((3 - x - y) - 1), 
      mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
      mul_pos (show 0 < x by linarith) (show 0 < 3 - x - y by nlinarith), 
      mul_pos (show 0 < y by linarith) (show 0 < 3 - x - y by nlinarith)
      ]
  have h5 : (3 * (3 / 2 : ℝ) ^ 3) ^ 4 / ((3 / 2) ^ 4 + 2 * (3 / 2) ^ 4 + 3 * (3 / 2) ^ 4) ^ 3 = 3 / 8 := by 
    norm_num
  linarith [h2, h5]