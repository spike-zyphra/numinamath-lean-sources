import Mathlib

theorem inequalities_172733 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) +
    (3 * z ^ 2 - z) / (1 + z ^ 2) ≥ 0 := by

  have hx2 : 0 < x ^ 2 := by nlinarith 
  have hy2 : 0 < y ^ 2 := by nlinarith
  have hz2 : 0 < z ^ 2 := by nlinarith
  have hx2_pos : 0 < 1 + x ^ 2 := by nlinarith
  have hy2_pos : 0 < 1 + y ^ 2 := by nlinarith 
  have hz2_pos : 0 < 1 + z ^ 2 := by nlinarith

  have h2 : (3 * x ^ 2 - x) / (1 + x ^ 2) + (3 * y ^ 2 - y) / (1 + y ^ 2) + (3 * z ^ 2 - z) / (1 + z ^ 2) = 
    ( (3 * x ^ 2 - x) * (1 + y ^ 2) * (1 + z ^ 2) + (3 * y ^ 2 - y) * (1 + x ^ 2) * (1 + z ^ 2) + (3 * z ^ 2 - z) * (1 + x ^ 2) * (1 + y ^ 2) ) / ( (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2) ) := by 
    field_simp 
    <;> ring

  rw [h2] 
  apply div_nonneg
  have h3 : (3 * x ^ 2 - x) * (1 + y ^ 2) * (1 + z ^ 2) + (3 * y ^ 2 - y) * (1 + x ^ 2) * (1 + z ^ 2) + (3 * z ^ 2 - z) * (1 + x ^ 2) * (1 + y ^ 2) ≥ 0 := by 
    have h1 : z = 1 - x - y := by 
      linarith 
    rw [h1] 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      sq_nonneg (x * y - x * (1 - x - y)), sq_nonneg (x * y - y * (1 - x - y)), 
      sq_nonneg (x * (1 - x - y) - y * (1 - x - y)), 
      mul_pos hx hy, mul_pos hx (show (1 - x - y : ℝ) > 0 by nlinarith), 
      mul_pos hy (show (1 - x - y : ℝ) > 0 by nlinarith), 
      mul_pos (show x * y > 0 by nlinarith) (show (1 - x - y : ℝ) > 0 by nlinarith)
    ]
  linarith 
  all_goals positivity