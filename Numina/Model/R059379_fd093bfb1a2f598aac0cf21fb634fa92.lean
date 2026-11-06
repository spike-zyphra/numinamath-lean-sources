import Mathlib

theorem algebra_11688 (p n d q : ℚ) (hp : p = 1 / 2) (hn : n = 1 / 2)
    (hd : d = 1 / 2) (hq : q = 1 / 2) :
    p * n = 1 / 4 := by
  rw [hp, hn]
  norm_num