import Mathlib

theorem number_theory_9590 {n : ℕ} (hn : n = 2023) :
    Nat.digits 5 n = [3, 4, 0, 1, 3] := by 
  rw [hn]
  norm_num