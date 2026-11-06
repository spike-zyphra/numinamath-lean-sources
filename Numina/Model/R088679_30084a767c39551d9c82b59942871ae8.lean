import Mathlib

theorem algebra_1374 {m : ℝ} (h : m ≠ 0) (h1 : m - 1/m = -3) :
    m^3 - 1/m^3 = -36 := by
  have h2 : m^3 - 1/m^3 = (m - 1/m)^3 + 3 * (m - 1/m) := by
    field_simp [h]
    ring
  rw [h2, h1]
  norm_num