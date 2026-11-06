import Mathlib

theorem algebra_177850 {x : ℝ} (hx : x > 0) (h : 100 / x = 120 / (x + 100)) :
    x = 500 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : x + 100 ≠ 0 := by nlinarith
  field_simp [h1, h2] at h
  nlinarith