import Mathlib

theorem algebra_143225 {I : ℝ} (hI : I = 0.5 / 6) :
    I * 48 = 4 := by
  rw [hI]
  norm_num