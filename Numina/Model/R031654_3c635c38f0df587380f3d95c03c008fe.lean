import Mathlib

theorem number_theory_5000 (m a s t: ℕ)(ham : Nat.Coprime a m) [Fintype (ZMod m)ˣ](ht : 0 < t)
    (hord : orderOf (ZMod.unitOfCoprime a ham) = s * t) :
    orderOf ((ZMod.unitOfCoprime a ham) ^ t) = s := by
  rw [orderOf_pow, hord]
  have h1 : Nat.gcd (s * t) t = t := by 
    simp [Nat.gcd_comm, Nat.mul_comm]
  simp [h1]
  all_goals field_simp at *
  <;> nlinarith