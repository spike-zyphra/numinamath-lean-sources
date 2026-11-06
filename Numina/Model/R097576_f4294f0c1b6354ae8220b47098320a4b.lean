import Mathlib

theorem algebra_3578 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = -2) :
    (x + 1) ^ 100 = 0 := by
  have h1 : x ^ 2 + 2 * x + 1 = 0 := by
    field_simp [hx] at h
    nlinarith
  have h2 : (x + 1) ^ 2 = 0 := by
    nlinarith
  have h3 : x + 1 = 0 := by
    nlinarith
  rw [h3]
  norm_num