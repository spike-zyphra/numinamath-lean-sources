import Mathlib

theorem inequalities_1607 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (y + z) ≥ 3 / 4 * x / (x + y + z) + 3 / 4 * x ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) := by
  have pos1 : 0 < y + z := by nlinarith
  have pos2 : 0 < x + y + z := by nlinarith
  have pos3 : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h1 : 0 < 4 * (y + z) * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) := by positivity
  have h2 : x / (y + z) - (3 / 4 * x / (x + y + z) + 3 / 4 * x ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2)) ≥ 0 := by
    have h3 : (x / (y + z) - (3 / 4 * x / (x + y + z) + 3 / 4 * x ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2))) =
        (4 * x * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) - (3 * x * (x ^ 2 + y ^ 2 + z ^ 2) + 3 * x ^ 2 * (x + y + z)) * (y + z)) / (4 * (y + z) * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2)) := by
      field_simp
      ring
    rw [h3]
    have h4 : 0 ≤ 4 * x * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) - (3 * x * (x ^ 2 + y ^ 2 + z ^ 2) + 3 * x ^ 2 * (x + y + z)) * (y + z) := by
      nlinarith [sq_nonneg (x * (x - y) + x * (x - z) + y * (y - z)), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x * (x + y + z) - y * (x + y + z)), sq_nonneg (x * (x + y + z) - z * (x + y + z)), sq_nonneg (y * (y + z) - z * (x + y + z)), sq_nonneg (y * (x + y + z) - z * (x + y + z)), sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    exact div_nonneg h4 (by positivity)
  linarith