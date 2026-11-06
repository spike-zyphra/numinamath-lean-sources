import Mathlib

/- Show that if \(\bar{a}\) is an inverse of \(a\) modulo \(n\), then \(\operatorname{ord}_{n} a = \operatorname{ord}_{n} \bar{a}\).-/
theorem number_theory_4995 (n a: ℕ) (hna : Nat.Coprime a n) :
    orderOf (ZMod.unitOfCoprime a hna) = orderOf ((ZMod.unitOfCoprime a hna)⁻¹) :=
  --this is exactly the proposition orderOf_inv in Mathlib
  symm (orderOf_inv (ZMod.unitOfCoprime a hna))
