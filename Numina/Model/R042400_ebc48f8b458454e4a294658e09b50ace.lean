import Mathlib

theorem inequalities_129086 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) +
        (z - x) / (z * x + 2 * x + 1) := by
  have hx1 : 0 < x * y + 2 * y + 1 := by
    positivity
  have hy1 : 0 < y * z + 2 * z + 1 := by
    positivity
  have hz1 : 0 < z * x + 2 * x + 1 := by
    positivity
  have h : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) =
      ((x - y) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1) +
      (y - z) * (x * y + 2 * y + 1) * (z * x + 2 * x + 1) +
      (z - x) * (x * y + 2 * y + 1) * (y * z + 2 * z + 1)) / ((x * y + 2 * y + 1) * (y * z + 2 * z + 1) * (z * x + 2 * x + 1)) := by
    field_simp
    <;> ring
  rw [h] at *
  apply div_nonneg
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
    mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx
  ]
  all_goals positivity