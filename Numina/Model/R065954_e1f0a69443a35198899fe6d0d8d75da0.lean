import Mathlib

theorem algebra_5833 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 3) :
    x^4 + 1/x^4 = 47 := by
  have h1 : x^2 + 1 / x^2 = 7 := by
    have eq1 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by 
      field_simp [hx]
      ring
    rw [eq1, h]
    norm_num
  have h2 : x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by
    field_simp [hx]
    ring
  rw [h2, h1]
  norm_num