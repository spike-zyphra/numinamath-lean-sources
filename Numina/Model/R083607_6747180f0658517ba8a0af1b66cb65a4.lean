import Mathlib

theorem number_theory_6947 {n m : ℕ} (hn : n = 0b1111) (hm : m = 0b101) : n / m = 0b11 := by 
  subst hn
  subst hm
  all_goals norm_num