import Mathlib

theorem algebra_14548 {n : ℕ} (hn : n = 20) :
    (n * (n - 3)) / 2 = 170 := by 
  subst hn
  norm_num