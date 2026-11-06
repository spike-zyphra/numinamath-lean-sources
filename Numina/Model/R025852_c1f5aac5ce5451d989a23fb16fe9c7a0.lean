import Mathlib

theorem number_theory_19422 (x : ℕ) (h : x = Nat.ofDigits 3 [2, 2, 2, 1]) : x = 53 := by
  rw [h]
  norm_num [Nat.ofDigits]