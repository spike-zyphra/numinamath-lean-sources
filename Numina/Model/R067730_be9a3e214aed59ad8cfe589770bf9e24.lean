import Mathlib

theorem algebra_110790 (l t : ℝ) (hl : l = 280) (ht : t = 20) (v : ℝ) (hv : v = 18) :
    l + v * t = 640 := by
  rw [hl, ht, hv]
  norm_num