import Mathlib

theorem number_theory_23232 {n : ℕ} (hn : n = 222) :
    Nat.digits 13 n = [1, 4, 1] := by
  rw [hn]
  norm_num