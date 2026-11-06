import Mathlib
/-Find $10110_2\times10100_2\div10_2$. Express your answer in base 2.-/
theorem number_theory_5438(a b c:ℕ)(ha:(Nat.digits 2 a)= [0, 1, 1, 0, 1])(hb:Nat.digits 2 b= [0, 0, 1, 0, 1])(hc:Nat.digits 2 c =[0 ,1]): Nat.digits 2 (a*b/c) = [0, 0, 1, 1, 1, 0, 1, 1] := by
-- use injective of digits
have h1:=Nat.digits.injective 2
-- prove a=22 b=20 c=2
have ha:a=22:= by apply h1;rw [ha];native_decide
have hb:b=20:= by apply h1;rw [hb];native_decide
have hc:c=2:=by apply h1;rw [hc];native_decide
-- prove result
rw [ha,hb,hc]
native_decide

