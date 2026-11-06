import Mathlib

theorem number_theory_18638 {a b : ℕ}
    (ha: Nat.digits 3 a = [2,1,0,2])
    (hb: Nat.digits 3 b = [1,0,2]):
    Nat.digits 3 (a * b) = [2, 1, 1, 2, 1, 1, 1] := by
  have ha1 : a = 59 := by 
    rw [← Nat.ofDigits_digits 3 a]
    rw [ha]
    norm_num [Nat.ofDigits]
  have hb1 : b = 19 := by
    rw [← Nat.ofDigits_digits 3 b]
    rw [hb]
    norm_num [Nat.ofDigits]
  calc 
    Nat.digits 3 (a * b) = Nat.digits 3 (59 * 19) := by rw [ha1, hb1]
    _ = Nat.digits 3 1121 := by norm_num
    _ = [2, 1, 1, 2, 1, 1, 1] := by norm_num