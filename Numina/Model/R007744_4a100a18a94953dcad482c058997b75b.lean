import Mathlib

theorem inequalities_69782 {P Q : ℕ}
    (hP : P = Nat.ofDigits 10 (List.replicate 2010 8) * Nat.ofDigits 10 (List.replicate 2010 3))
    (hQ : Q = Nat.ofDigits 10 (List.replicate 2010 4) * Nat.ofDigits 10 (7 :: List.replicate 2009 6)) :
    Q > P := by 
  rw [hP, hQ]
  native_decide