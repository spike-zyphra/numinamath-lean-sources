import Mathlib

theorem number_theory_15286 (n : ℕ) (h : Nat.digits 7 n = [5, 3, 1]) : n = 75 := by 
  rw [← Nat.ofDigits_digits 7 n]
  rw [h]
  norm_num [Nat.ofDigits]