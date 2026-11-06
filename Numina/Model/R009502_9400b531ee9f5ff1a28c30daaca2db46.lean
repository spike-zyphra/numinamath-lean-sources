import Mathlib

theorem algebra_14317 {n m : ℕ} (hn : n = 20) (hm : m = 15) :
    n * m + n * (n - 1) / 2 = 490 := by
  subst hn
  subst hm
  norm_num