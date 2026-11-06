import Mathlib

/- Show that if \( p \) is a prime number and \( a \) is a positive integer, then \( a^{p} \equiv a \mod p \).-/
theorem number_theory_4777 (p a : ℕ) (hp : Nat.Prime p) (_ : 0 < a) :
    a^p ≡ a [MOD p] := by
  -- exactly `ZMod.pow_card` in Mathlib
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat]
  push_cast
  apply ZMod.pow_card
