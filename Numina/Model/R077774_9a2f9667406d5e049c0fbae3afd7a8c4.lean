import Mathlib

theorem inequalities_598052 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (y + z) + y / (z + x) + z / (x + y) ≥ 3 / 2 := by
  have h1 : 0 < x + y + z := by linarith
  have h3 : 0 < y + z := by linarith
  have h4 : 0 < z + x := by linarith
  have h5 : 0 < x + y := by linarith

  have h2 : x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2 ≥ 0 := by
    have h6 : x / (y + z) + y / (z + x) + z / (x + y) - 3 / 2 =
        (2 * x * (z + x) * (x + y) + 2 * y * (y + z) * (x + y) + 2 * z * (y + z) * (z + x) - 3 * (y + z) * (z + x) * (x + y))
          / (2 * (y + z) * (z + x) * (x + y)) := by
      field_simp
      ring
    rw [h6]
    have h7 : 0 < 2 * (y + z) * (z + x) * (x + y) := by positivity
    have h8 : 2 * x * (z + x) * (x + y) + 2 * y * (y + z) * (x + y) + 2 * z * (y + z) * (z + x) - 3 * (y + z) * (z + x) * (x + y) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_pos_of_pos (show 0 < x by linarith), sq_pos_of_pos (show 0 < y by linarith), sq_pos_of_pos (show 0 < z by linarith),
        sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y)]
    apply div_nonneg
    linarith
    positivity
  linarith