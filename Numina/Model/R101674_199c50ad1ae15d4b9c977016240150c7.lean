import Mathlib

theorem algebra_4499 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 4) : x ^ 4 + 1 / x ^ 4 = 194 := by 
  have h1 : x ^ 2 + 1 / x ^ 2 = 14 := by
    have h2 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
      field_simp
      ring
    rw [h2, h]
    norm_num
  have h3 : x ^ 4 + 1 / x ^ 4 = (x ^ 2 + 1 / x ^ 2) ^ 2 - 2 := by
    field_simp
    ring
  rw [h3, h1]
  norm_num