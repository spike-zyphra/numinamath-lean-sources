import Mathlib

/- Given that $13^{-1} \equiv 29 \pmod{47}$, find $34^{-1} \pmod{47}$, as a residue modulo 47.  (Give a number between 0 and 46, inclusive.) -/
theorem number_theory_15850 (_ : Nat.ModEq 47 (13 * 29) 1) : 34 * 18 ≡ 1 [MOD 47] := by 
  rfl
