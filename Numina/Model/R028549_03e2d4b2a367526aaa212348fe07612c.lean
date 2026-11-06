import Mathlib

theorem inequalities_603558 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) ≥ 0 := by

  have hx1 : 0 < z + x := by nlinarith
  have hy1 : 0 < x + y := by nlinarith
  have hz1 : 0 < y + z := by nlinarith
  
  have h3 : (y ^ 2 - x ^ 2) / (z + x) + (z ^ 2 - y ^ 2) / (x + y) + (x ^ 2 - z ^ 2) / (y + z) =
      ((y ^ 2 - x ^ 2) * (x + y) * (y + z) + (z ^ 2 - y ^ 2) * (z + x) * (y + z) + (x ^ 2 - z ^ 2) * (z + x) * (x + y)) / ((z + x) * (x + y) * (y + z)) := by 
    field_simp
    ring

  rw [h3]

  have hx2 : (z + x) * (x + y) * (y + z) > 0 := by
    positivity
  
  have hx3 : ((y ^ 2 - x ^ 2) * (x + y) * (y + z) + (z ^ 2 - y ^ 2) * (z + x) * (y + z) + (x ^ 2 - z ^ 2) * (z + x) * (x + y)) ≥ 0 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_pos (show 0 < x + y by nlinarith) (show 0 < y + z by nlinarith), 
      mul_pos (show 0 < x + y by nlinarith) (show 0 < z + x by nlinarith), 
      mul_pos (show 0 < y + z by nlinarith) (show 0 < z + x by nlinarith)
    ]
  
  apply div_nonneg 
  linarith 
  positivity