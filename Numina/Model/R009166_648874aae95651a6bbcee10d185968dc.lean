import Mathlib
theorem number_theory_5438(a b c:ℕ)(ha:(Nat.digits 2 a)= [0, 1, 1, 0, 1])(hb:Nat.digits 2 b= [0, 0, 1, 0, 1])(hc:Nat.digits 2 c =[0 ,1]): Nat.digits 2 (a*b/c) = [0, 0, 1, 1, 1, 0, 1, 1] := by
  have ha2: a=22 := by 
    rw [← Nat.ofDigits_digits 2 a]
    rw [ha]
    norm_num [Nat.ofDigits]
    all_goals linarith
  have hb2: b=20 := by 
    rw [← Nat.ofDigits_digits 2 b]
    rw [hb]
    norm_num [Nat.ofDigits]
    all_goals linarith
  have hc2: c=2 := by 
    rw [← Nat.ofDigits_digits 2 c]
    rw [hc]
    norm_num [Nat.ofDigits]
    all_goals linarith
  rw [ha2,hb2,hc2]
  all_goals norm_num [Nat.digits, Nat.digitsAux]