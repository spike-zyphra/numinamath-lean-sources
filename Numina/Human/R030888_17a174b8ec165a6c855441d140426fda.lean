import Mathlib

theorem algebra_187681 (x : ℝ) (hx : x ≠ 0) :
    (1 - 25 / 100) * x * (1 + 30 / 100) / x < 1 := by
  have h1 : (1 - 25 / 100 : ℝ) * x * (1 + 30 / 100) / x = (1 - 25 / 100) * (1 + 30 / 100) := by
    field_simp [hx]
    ring
  rw [h1]
  norm_num