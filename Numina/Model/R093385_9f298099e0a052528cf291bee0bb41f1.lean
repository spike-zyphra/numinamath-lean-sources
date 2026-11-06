import Mathlib

theorem algebra_141965 (p q : ℝ) (hp : p = 0.9) (hq : q = 0.85) :
    p * q = 0.765 := by
  rw [hp, hq]
  norm_num