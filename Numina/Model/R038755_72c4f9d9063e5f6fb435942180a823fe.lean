import Mathlib

theorem number_theory_23126 (a b c d e : ℕ) (ha :  a = Nat.ofDigits 7 [1, 2, 3, 4]) (hb : b = Nat.ofDigits 7 [3, 2, 1]) (hc : c = Nat.ofDigits 7 [2, 3]) (hd : d = Nat.ofDigits 7 [1, 2]) (he : e = Nat.ofDigits 7 [1]) : Nat.digits 7 (a - b + c - d + e) = [0, 1, 2, 4] := by 
  rw [ha, hb, hc, hd, he]
  norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]