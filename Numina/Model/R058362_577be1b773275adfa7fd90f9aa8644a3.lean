import Mathlib

theorem algebra_279881 (x : ℝ) (hx : x > 0) (h : 165 / x = 3 / 8) :
    x - 165 = 275 := by
  have hx' : x ≠ 0 := by linarith
  field_simp [hx'] at h
  have hx_eq : x = 440 := by
    linarith
  linarith [hx_eq]