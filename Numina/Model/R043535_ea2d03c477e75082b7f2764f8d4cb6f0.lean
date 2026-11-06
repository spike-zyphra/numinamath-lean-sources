import Mathlib

theorem number_theory_221640 (N p : ℕ) (hp : Nat.Prime p) (h : ¬p ∣ N) :
    p ∣ N^(p - 1) - 1 := by
  have h1 : 1 ≤ p := Nat.Prime.one_le hp
  have h2 : N ^ (p - 1) ≡ 1 [MOD p] := by 
    have h3 : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.eq_iff_modEq_nat p]
    simp [ZMod.pow_card_sub_one_eq_one, ZMod.natCast_zmod_eq_zero_iff_dvd, h]
  have h3 : p ∣ (N ^ (p - 1) - 1) := by
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)
  exact h3