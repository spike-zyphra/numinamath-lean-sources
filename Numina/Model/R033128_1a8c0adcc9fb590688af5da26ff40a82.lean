import Mathlib

theorem number_theory_278802 (p : ℕ) (hp : Nat.Prime p) (a : ℕ) :
    p ∣ a^p - a := by
  have h1 : a ^ p ≡ a [MOD p] := by
    have h2 : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.eq_iff_modEq_nat p]
    simp [ZMod.pow_card]

  have h2 : (a ^ p - a) % p = 0 := by
    rw [Nat.sub_mod_eq_zero_of_mod_eq h1]

  exact Nat.dvd_of_mod_eq_zero h2