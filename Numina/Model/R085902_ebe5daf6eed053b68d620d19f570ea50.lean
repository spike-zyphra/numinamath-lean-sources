import Mathlib

theorem algebra_163361 {x : ℝ} (hx : x > 0) (h : 100 / x = 120 / (x + 100)) :
    x = 500 := by
  have h1 : x + 100 ≠ 0 := by
    linarith
  have h2 : x ≠ 0 := by
    linarith
  field_simp [h2, h1] at h
  linarith