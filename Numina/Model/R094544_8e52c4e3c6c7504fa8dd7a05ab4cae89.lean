import Mathlib

theorem algebra_19327 {x : ℝ} (hx : x = 15 * 1500) (h : x / 2500 = y) :
    y = 9 := by
  rw [hx] at h
  linarith