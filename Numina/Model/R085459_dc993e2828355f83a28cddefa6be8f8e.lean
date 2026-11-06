import Mathlib

theorem algebra_275400 {p q : ℝ} (h : p * 2 + q * (-4) = 8) (h' : 3 * 2 - q * (-4) = 38) :
    p = 20 := by
  have hq : q = 8 := by
    linarith
  rw [hq] at h
  linarith