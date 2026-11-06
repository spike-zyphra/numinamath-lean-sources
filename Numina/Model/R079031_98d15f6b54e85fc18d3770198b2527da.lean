import Mathlib

theorem algebra_21712 (n : ℕ) (hn : n = 9) :
    n * (n - 1) * (n - 2) * (n - 3) = 3024 := by 
  subst hn
  norm_num