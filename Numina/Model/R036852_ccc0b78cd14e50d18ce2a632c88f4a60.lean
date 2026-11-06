import Mathlib

theorem inequalities_166066 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x + y) * (x + z) * (y + z)) / (4 * x * y * z) ≥ (x + z) / (y + z) + (y + z) / (x + z) := by
  have hx1 : 0 < x * y * z := by
    positivity
  have hx2 : 0 < 4 * x * y * z := by
    positivity
  have hx3 : 0 < y + z := by
    nlinarith
  have hx4 : 0 < x + z := by
    nlinarith
  have h1 : ((x + y) * (x + z) * (y + z)) / (4 * x * y * z) - ((x + z) / (y + z) + (y + z) / (x + z)) ≥ 0 := by
    have hx5 : 0 < 4 * x * y * z * (y + z) * (x + z) := by
      positivity
    have h2 : ((x + y) * (x + z) * (y + z)) / (4 * x * y * z) - ((x + z) / (y + z) + (y + z) / (x + z)) =
        ((x + y) * (x + z) ^ 2 * (y + z) ^ 2 - 4 * x * y * z * (x + z) ^ 2 - 4 * x * y * z * (y + z) ^ 2) / (4 * x * y * z * (x + z) * (y + z)) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (x * y - x * z), sq_nonneg (x * z - y * z),
        sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (y - z)),
        sq_nonneg (y * (x - y)), sq_nonneg (y * (x - z)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (x - y)), sq_nonneg (z * (x - z)), sq_nonneg (z * (y - z)), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
        mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith),
        mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith),
        mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith)
      ]
    all_goals
      positivity
  linarith [h1]