import Mathlib

theorem inequalities_162274 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 5 ≤ (x + y - z)^2 / ((x + y)^2 + z^2) + (y + z - x)^2 / ((y + z)^2 + x^2) +
    (z + x - y)^2 / ((z + x)^2 + y^2) := by
  have h2 : 0 < (x + y)^2 + z^2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h3 : 0 < (y + z)^2 + x^2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h4 : 0 < (z + x)^2 + y^2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h5 : (x + y - z)^2 / ((x + y)^2 + z^2) + (y + z - x)^2 / ((y + z)^2 + x^2) +
    (z + x - y)^2 / ((z + x)^2 + y^2) - 3 / 5 ≥ 0 := by 
    have h6 : 0 < ((x + y)^2 + z^2) * ((y + z)^2 + x^2) * ((z + x)^2 + y^2) := by
      positivity
    have h7 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) +
      (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) - 3 / 5 =
      ((x + y - z) ^ 2 * ((y + z)^2 + x^2) * ((z + x)^2 + y^2) +
      (y + z - x) ^ 2 * ((x + y)^2 + z^2) * ((z + x)^2 + y^2) +
      (z + x - y) ^ 2 * ((x + y)^2 + z^2) * ((y + z)^2 + x^2) - 
      (3 / 5) * ((x + y)^2 + z^2) * ((y + z)^2 + x^2) * ((z + x)^2 + y^2)) / 
      (((x + y)^2 + z^2) * ((y + z)^2 + x^2) * ((z + x)^2 + y^2)) := by 
      field_simp
      ring
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)),
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    all_goals positivity
  linarith