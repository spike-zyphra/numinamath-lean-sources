import Mathlib

theorem number_theory_114336 {n : ℕ} (hn : Nat.digits 7 n = [3, 4]) :
    Nat.digits 9 n = [4, 3] := by
  have h1 : n = 31 := by 
    rw [← Nat.ofDigits_digits 7 n]
    rw [hn]
    norm_num [Nat.ofDigits]
  rw [h1]
  norm_num