import Mathlib

theorem number_theory_12345{a b : ℕ}
  (ha: Nat.digits 4 a = [0, 2, 1])
  (hb: Nat.digits 4 b = [3, 1])
  (hc: Nat.digits 4 c = [2]):
  Nat.digits 4 (a * b / c) = [0, 1, 1, 1] := by
  have ha2 : a = 24 := by 
    rw [← Nat.ofDigits_digits 4 a]
    rw [ha]
    norm_num [Nat.ofDigits]
  have hb2 : b = 7 := by
    rw [← Nat.ofDigits_digits 4 b]
    rw [hb]
    norm_num [Nat.ofDigits]
  have hc2 : c = 2 := by
    rw [← Nat.ofDigits_digits 4 c]
    rw [hc]
    norm_num [Nat.ofDigits]
  rw [ha2, hb2, hc2]
  all_goals norm_num