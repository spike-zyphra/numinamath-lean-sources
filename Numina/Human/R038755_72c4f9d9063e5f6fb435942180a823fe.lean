import Mathlib

/- Find $4321_{7}-123_{7}+32_{7}-21_{7}+1_{7}$. Express your answer in base $7$. -/
theorem number_theory_23126 (a b c d e : ℕ) (ha :  a = Nat.ofDigits 7 [1, 2, 3, 4]) (hb : b = Nat.ofDigits 7 [3, 2, 1]) (hc : c = Nat.ofDigits 7 [2, 3]) (hd : d = Nat.ofDigits 7 [1, 2]) (he : e = Nat.ofDigits 7 [1]) : Nat.digits 7 (a - b + c - d + e) = [0, 1, 2, 4] := by
  -- use Nat.ofDigits_cons to solve a, b, c, d, e by recursion
  repeat rw [Nat.ofDigits_cons] at ha
  repeat rw [Nat.ofDigits_cons] at hb
  repeat rw [Nat.ofDigits_cons] at hc
  repeat rw [Nat.ofDigits_cons] at hd
  -- calculate a, b, c, d, e
  simp at ha hb hc hd he
  -- substitute a, b, c, d, e
  rw [ha, hb, hc, hd, he]
  -- trivial calculation
  simp
