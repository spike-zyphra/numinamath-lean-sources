import Mathlib

theorem number_theory_234599 {n : ℕ} (hn : n = 21996) :
    n / 12 = 1833 ∧ n % 12 = 0 := by 
  subst hn
  constructor
  · norm_num
  · norm_num