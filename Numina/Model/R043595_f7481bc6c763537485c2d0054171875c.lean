import Mathlib

theorem inequalities_268878 (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z)
    (h : 1/x + 1/y + 1/z = 2) : 8 * (x - 1) * (y - 1) * (z - 1) ≤ 1 := by
  have h1 : x * y * z > 0 := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have eq1 : y * z + x * z + x * y = 2 * (x * y * z) := by
    have h2 : x * y * z > 0 := h1
    field_simp [h2] at h
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy), mul_pos (sub_pos.mpr hx) (sub_pos.mpr hz), mul_pos (sub_pos.mpr hy) (sub_pos.mpr hz)]