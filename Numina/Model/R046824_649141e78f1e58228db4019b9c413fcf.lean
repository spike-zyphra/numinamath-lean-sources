import Mathlib

theorem inequalities_200500 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / (1 + x + 1 / y) + 1 / (1 + y + 1 / z) + 1 / (1 + z + 1 / x) ≤ 1 := by
  have h4 : 1 / (1 + x + 1 / y) = y / (y + x * y + 1) := by 
    field_simp [hy.ne.symm]
    <;> ring
  have h5 : 1 / (1 + y + 1 / z) = z / (z + y * z + 1) := by 
    field_simp [hz.ne.symm]
    <;> ring
  have h6 : 1 / (1 + z + 1 / x) = x / (x + z * x + 1) := by 
    field_simp [hx.ne.symm]
    <;> ring
  rw [h4, h5, h6]
  have h10 : 0 < (y + x * y + 1) * (z + y * z + 1) * (x + z * x + 1) := by
    positivity
  have h11 : y / (y + x * y + 1) + z / (z + y * z + 1) + x / (x + z * x + 1) - 1 ≤ 0 := by
    have h13 : y / (y + x * y + 1) + z / (z + y * z + 1) + x / (x + z * x + 1) - 1 =
        (y * (z + y * z + 1) * (x + z * x + 1) + z * (y + x * y + 1) * (x + z * x + 1) + x * (y + x * y + 1) * (z + y * z + 1) - (y + x * y + 1) * (z + y * z + 1) * (x + z * x + 1)) / ((y + x * y + 1) * (z + y * z + 1) * (x + z * x + 1)) := by
      field_simp
      <;> ring
    rw [h13]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
              sq_nonneg (x * y * z - 1), 
              mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
              mul_pos (mul_pos hx hy) hz
            ]
    all_goals
      positivity
  linarith