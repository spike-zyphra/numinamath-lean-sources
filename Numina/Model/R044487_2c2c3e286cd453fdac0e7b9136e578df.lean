import Mathlib

open Set

theorem algebra_5185 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 5) :
    x^4 + 1/x^4 = 527 := by

  have h1 : x^2 + 1/x^2 = 23 := by
    have eq1 : x^2 + 1/x^2 = (x + 1/x)^2 - 2 := by
      field_simp
      ring
    rw [eq1, h]
    norm_num

  have h2 : x^4 + 1/x^4 = (x^2 + 1/x^2)^2 - 2 := by
    field_simp
    ring

  rw [h2, h1]
  all_goals norm_num