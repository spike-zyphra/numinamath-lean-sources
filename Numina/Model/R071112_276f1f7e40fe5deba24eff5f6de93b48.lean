import Mathlib

theorem number_theory_261197 {n : ℕ} (hn : n = 989010989) :
    (n * 123456789) % 1000000000 = 987654321 := by 
  subst n
  norm_num