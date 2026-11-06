import Mathlib

theorem algebra_203392 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 1) :
    x ^ 5 + 1 / x ^ 5 = 1 := by
  have h1 : x^2 - x + 1 = 0 := by
    field_simp at h
    nlinarith
  
  have h2 : x^2 - x + 1 > 0 := by
    nlinarith [sq_nonneg (x - 1 / 2)]

  linarith [h1, h2]