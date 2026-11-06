import Mathlib

theorem number_theory_248813 (x : ℝ) (hx : x = 100 * (97.22 / 100)) : x = 97.22 := by
  rw [hx]
  norm_num