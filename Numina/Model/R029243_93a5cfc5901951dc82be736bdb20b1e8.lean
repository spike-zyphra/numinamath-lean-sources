import Mathlib

theorem inequalities_77960 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    ((x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y) ≥ x + y + z := by 
  have h4 : (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y - (x + y + z) ≥ 0 := by
    have hx5 : 0 < x * y * z := by
      nlinarith
    have hx6 : (x + y - 1)^2 / z + (y + z - 1)^2 / x + (z + x - 1)^2 / y - (x + y + z) =
        ((x + y - 1) ^ 2 * (x * y) + (y + z - 1) ^ 2 * (y * z) + (z + x - 1) ^ 2 * (x * z) - (x + y + z) * (x * y * z)) / (x * y * z) := by 
      field_simp 
      ring
    rw [hx6] at *
    apply div_nonneg 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        h, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx 
        ]
    all_goals
      positivity
  linarith