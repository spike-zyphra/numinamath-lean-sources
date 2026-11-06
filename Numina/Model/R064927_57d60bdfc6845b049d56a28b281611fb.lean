import Mathlib

theorem number_theory_18560 (n : ℕ) (h : Nat.digits 5 n = [0, 1, 0, 1, 0, 1]) : n = 3255 := by 
  rw [← Nat.ofDigits_digits 5 n]
  rw [h]
  norm_num [Nat.ofDigits]