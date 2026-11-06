import Mathlib

theorem algebra_180580 (x y : ℝ) (hx : x ≠ 0) (h : 15 / 100 * x = 20 / 100 * y) :
    y / x * 100 = 75 := by
  have h1 : 15 * x = 20 * y := by
    linarith
  have h2 : y / x = 3 / 4 := by
    field_simp [hx]
    linarith
  rw [h2]
  all_goals norm_num