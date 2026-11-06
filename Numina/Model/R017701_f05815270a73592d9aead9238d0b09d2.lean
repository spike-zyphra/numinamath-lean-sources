import Mathlib

theorem inequalities_53 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (x + y) / (1 + x * y) + (y + z) / (1 + y * z) + (z + x) / (1 + z * x) ≤
    9 / (2 * (x + y + z)) := by
  have hx1 : 0 < x * y := by nlinarith 
  have hy1 : 0 < y * z := by nlinarith 
  have hz1 : 0 < z * x := by nlinarith 
  have h1 : 0 < 1 + x * y := by linarith 
  have h2 : 0 < 1 + y * z := by linarith 
  have h3 : 0 < 1 + z * x := by linarith 
  have h4 : 0 < x + y + z := by nlinarith 
  have h5 : 0 < 2 * (x + y + z) := by linarith 
  have h6 : (x + y) / (1 + x * y) + (y + z) / (1 + y * z) + (z + x) / (1 + z * x) - 9 / (2 * (x + y + z)) ≤ 0 := by 
    have h7 : 0 < (1 + x * y) * (1 + y * z) * (1 + z * x) * (2 * (x + y + z)) := by positivity 
    have h8 : (x + y) / (1 + x * y) + (y + z) / (1 + y * z) + (z + x) / (1 + z * x) - 9 / (2 * (x + y + z)) = 
      ( (x + y) * (1 + y * z) * (1 + z * x) * (2 * (x + y + z)) + (y + z) * (1 + x * y) * (1 + z * x) * (2 * (x + y + z)) + (z + x) * (1 + x * y) * (1 + y * z) * (2 * (x + y + z)) - 9 * (1 + x * y) * (1 + y * z) * (1 + z * x) ) / ( (1 + x * y) * (1 + y * z) * (1 + z * x) * (2 * (x + y + z) ) ) := by 
      field_simp 
      ring 
    rw [h8] at *
    apply div_nonpos_of_nonpos_of_nonneg 
    · -- Show the numerator is nonpositive
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
        mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
        mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
      ]
    · -- Show the denominator is nonnegative
      positivity 
  linarith