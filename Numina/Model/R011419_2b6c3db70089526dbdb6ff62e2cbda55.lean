import Mathlib

theorem inequalities_24815 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) ≥ 3 / 4:= by 
  have h4 : 0 < (1 + x) * (1 + y) * (1 + z) := by 
    positivity
  have h5 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h6 : x ^3 / ((1 + y) * (1 + z)) + y ^3 / ((1 + z) * (1 + x)) + z ^3 / ((1 + x) * (1 + y)) - 3 / 4 = 
      (4 * x ^3 * (1 + x) + 4 * y ^3 * (1 + y) + 4 * z ^3 * (1 + z) - 3 * (1 + x) * (1 + y) * (1 + z)) / (4 * (1 + x) * (1 + y) * (1 + z)) := by
      field_simp 
      ring
    rw [h6] at *
    have h7 : (4 * x ^3 * (1 + x) + 4 * y ^3 * (1 + y) + 4 * z ^3 * (1 + z) - 3 * (1 + x) * (1 + y) * (1 + z)) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
        h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith)
      ]
    apply div_nonneg
    linarith [h7]
    all_goals
      positivity
  linarith