import Mathlib

theorem number_theory_5456 {n : ℕ} (hn : n = 26) :
    Nat.factorial n % 29 = 14 := by 
  rw [hn]
  norm_num [Nat.factorial]