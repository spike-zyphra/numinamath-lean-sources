import Mathlib

theorem inequalities_599039 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 2 ≤ x / (y + z) + y / (z + x) + z / (x + y) := by
  have h1 : 0 < x + y := by linarith [hx, hy]
  have h2 : 0 < x + z := by linarith [hx, hz]
  have h3 : 0 < y + z := by linarith [hy, hz]
  have h4 : 0 < (y + z) * (z + x) * (x + y) := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h5 : x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2 ≥ 0 := by
    have h6 : (x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2) =
        (2 * x * (z + x) * (x + y) + 2 * y * (y + z) * (x + y) + 2 * z * (y + z) * (z + x) - 3 * (y + z) * (z + x) * (x + y)) / (2 * (y + z) * (z + x) * (x + y)) := by 
      field_simp
      ring
    rw [h6]
    have h7 : 2 * (y + z) * (z + x) * (x + y) > 0 := by
      positivity
    have h8 : 2 * x * (z + x) * (x + y) + 2 * y * (y + z) * (x + y) + 2 * z * (y + z) * (z + x) - 3 * (y + z) * (z + x) * (x + y) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    apply div_nonneg
    linarith
    positivity
  linarith