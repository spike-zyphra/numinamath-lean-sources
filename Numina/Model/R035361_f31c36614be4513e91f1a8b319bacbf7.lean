import Mathlib

theorem number_theory_19553 (h: x1 = Nat.ofDigits 5 [4,3,2,1]) (h2: x2 =  Nat.ofDigits 5 [1,4,3,2]) : Nat.digits 5 (x1+x2) = [0,3,1,4]:= by 
  rw [h, h2]
  norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]