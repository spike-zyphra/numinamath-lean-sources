import Mathlib

theorem number_theory_23508 {n : ℕ} (hn : n = Nat.ofDigits 16 [9, 2, 7]) :
    n % 15 = 3 := by 
  rw [hn]
  norm_num [Nat.ofDigits]