import Mathlib

theorem algebra_13903 {s : ℝ} (hs : s > 0) (h : 4 * s = 144) :
    2 * (s + s / 4) = 90 := by
  have hs_val : s = 36 := by
    linarith
  rw [hs_val]
  norm_num