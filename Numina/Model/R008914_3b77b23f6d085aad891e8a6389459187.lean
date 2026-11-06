import Mathlib

theorem number_theory_4995 (n a: ℕ) (hna : Nat.Coprime a n) :
    orderOf (ZMod.unitOfCoprime a hna) = orderOf ((ZMod.unitOfCoprime a hna)⁻¹) := by 
  rw [orderOf_inv]