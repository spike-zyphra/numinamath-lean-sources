import Mathlib

theorem inequalities_328184 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) ≤ 3 / 4 := by
  have h1 : 0 < 2 * x + y + z := by linarith only [hx, hy, hz]
  have h2 : 0 < x + 2 * y + z := by linarith only [hx, hy, hz];
  have h3 : 0 < x + y + 2 * z := by linarith only [hx, hy, hz];
  have h4 : x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4 ≤ 0 := by
    have pos1 : (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) > 0 := by positivity
    have h5 : (x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z) - 3 / 4) =
        ( (x * (x + 2 * y + z) * (x + y + 2 * z) + y * (2 * x + y + z) * (x + y + 2 * z) + z * (2 * x + y + z) * (x + 2 * y + z) - 3 / 4 * (2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z) ) / ((2 * x + y + z) * (x + 2 * y + z) * (x + y + 2 * z)) ) := by
      field_simp
      ring
      <;> field_simp
      <;> ring
    rw [h5]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator ≤ 0
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          h1, h2, h3
          ]
    · -- Show denominator ≥ 0
      positivity
  linarith
  all_goals positivity
  all_goals positivity
  all_goals positivity