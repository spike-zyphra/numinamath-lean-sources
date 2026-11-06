import Mathlib

/- Suppose $a$ is an integer such that $0 \le a \le 14$, and $235935623_{74}-a$ is a multiple of $15$. What is $a$? -/
theorem number_theory_14215
    (v a : ℤ)
    (hv : v = Nat.ofDigits 74 [3,2,6,5,3,9,5,3,2])
    (ha1 : 0 ≤ a) (ha2 : a ≤ 14)
    (hdiv : 15 ∣ v - a) :
    a = 0 := by

  -- Note that $235935623_{74}=3+2(74)+6(74)^2+5(74)^3+3(74)^4+9(74)^5+5(74)^6$ $+3(74)^7+2(74)^8$. But $74 \equiv -1 \mod{15}$, so this is just $3-2+6-5+3-9+5-3+2=0 \mod{15}$, so $a=\boxed{0}$.
  have hmodeq : 74 ≡ -1 [ZMOD 15] := by decide
  have : v ≡ 0 [ZMOD 15]:= by
    convert Nat.ofDigits_zmodeq' 74 (-1) 15 hmodeq [3,2,6,5,3,9,5,3,2]
  apply Dvd.dvd.modEq_zero_int at hdiv
  have : v - a ≡ 0 - a [ZMOD 15] := Int.ModEq.sub this rfl
  rw [zero_sub] at this
  have : -a ≡ 0 [ZMOD 15] := Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm hdiv)) this)
  interval_cases a
  any_goals norm_num at this
  any_goals contradiction
  rfl
