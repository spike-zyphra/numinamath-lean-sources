import Mathlib

theorem number_theory_4988 (a n u: ℕ)(_ : NeZero n) (_ : 0 < u)(han : Nat.Coprime a n) :
    orderOf ((ZMod.unitOfCoprime a han) ^ u) =
    orderOf (ZMod.unitOfCoprime a han) / Nat.gcd (orderOf (ZMod.unitOfCoprime a han)) u := by
  rw [orderOf_pow]
  all_goals
    try (simp [han])