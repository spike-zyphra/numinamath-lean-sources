import Mathlib

open Real

theorem inequalities_598403 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (y * z) + y / (z * x) + z / (x * y) ≥ 1 / x + 1 / y + 1 / z := by
  have h1 : x / (y * z) + y / (z * x) + z / (x * y) - (1 / x + 1 / y + 1 / z) ≥ 0 := by
    have h2 : x / (y * z) + y / (z * x) + z / (x * y) - (1 / x + 1 / y + 1 / z) =
      (x^2 + y^2 + z^2 - (y * z + x * z + x * y)) / (x * y * z) := by
      field_simp
      ring
    rw [h2]
    have h3 : x^2 + y^2 + z^2 - (y * z + x * z + x * y) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y - z), sq_nonneg (x + z - y), sq_nonneg (y + z - x)]
    have h4 : x * y * z > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    apply div_nonneg
    linarith
    all_goals positivity
  linarith