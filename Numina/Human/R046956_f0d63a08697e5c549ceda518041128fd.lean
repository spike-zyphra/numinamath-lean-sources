import Mathlib

/- Fermat's Little Theorem states that if \( p \) is a prime number and \( a \) is a positive integer such that \( p \) does not divide \( a \), then it follows that \( a^{p-1} \equiv 1 \mod p \).-/
theorem number_theory_4776 {a p : ℕ} (hp : p.Prime) (_ : 0 < a) (hap : ¬p ∣ a) :
    a^(p-1) ≡ 1 [MOD p] := by
  -- preparing some fact for `ZMod.pow_card_sub_one_eq_one`
  rw [← ZMod.eq_iff_modEq_nat]
  have : Fact p.Prime := ⟨hp⟩
  have : (a : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    simp
    intro h
    rw [← Nat.dvd_iff_mod_eq_zero] at h
    contradiction
  -- exact `ZMod.pow_card_sub_one_eq_one` in Mathlib
  have := ZMod.pow_card_sub_one_eq_one this
  push_cast
  assumption
