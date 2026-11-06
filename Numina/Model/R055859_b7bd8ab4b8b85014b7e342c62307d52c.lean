import Mathlib

theorem algebra_175495 (E : ℝ) (hE : E = (60 * 25 + 70 * 30 + 80 * 45) / 100) :
    E = 72 := by
  rw [hE]
  norm_num