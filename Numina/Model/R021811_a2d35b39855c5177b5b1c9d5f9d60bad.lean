import Mathlib

theorem inequalities_300953 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    x * y * z * (x + y) * (y + z) * (z + x) ≥
    (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) := by

  have h1 : 0 < x * y := by nlinarith
  have h2 : 0 < y * z := by nlinarith
  have h3 : 0 < z * x := by nlinarith

  have h4 : (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) =
      1 - (x^2 + y^2 + z^2) + (x^2 * y^2 + x^2 * z^2 + y^2 * z^2) - x^2 * y^2 * z^2 := by
    ring

  have h5 : x * y * z * (x + y) * (y + z) * (z + x) =
      x * y * z * ((x + y) * (y + z) * (z + x)) := by
    ring

  have h7 : x * y * z * (x + y) * (y + z) * (z + x) - (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
        mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith), 
        h]

  linarith