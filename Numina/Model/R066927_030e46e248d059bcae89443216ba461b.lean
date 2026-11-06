import Mathlib

theorem algebra_233999 (x : ℝ) (hx : x > 0) (h : (1 - 90 / 100) * x = (1 - 15 / x) * (1 - 60 / 100) * x) :
    x = 20 := by
  have h1 : x ≠ 0 := by linarith
  field_simp [h1] at h 
  nlinarith