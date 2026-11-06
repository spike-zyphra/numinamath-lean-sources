import Mathlib

theorem algebra_94502 {h l : ℝ} (hhl : h = l + 16) (havg : (h + l) / 2 = 3) :
l = -5 := by
  rw [hhl] at havg
  linarith