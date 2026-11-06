import Mathlib

/- Show that if \( a \) is an integer that is relatively prime to the positive integer \( m \) and the order of \( a \) modulo \( m \) is \( \operatorname{ord}_{m} a = s t \), then the order of \( a^t \) modulo \( m \) is \( \operatorname{ord}_{m} a^{t} = s \).-/
theorem number_theory_5000 (m a s t: ℕ)(ham : Nat.Coprime a m) [Fintype (ZMod m)ˣ](ht : 0 < t)
    (hord : orderOf (ZMod.unitOfCoprime a ham) = s * t) :
    orderOf ((ZMod.unitOfCoprime a ham) ^ t) = s := by
  --this is exactly the proposition orderOf_pow in Mathlib
  rw [orderOf_pow (ZMod.unitOfCoprime a ham), hord]; simp
  rw [Nat.mul_div_cancel]; exact ht
