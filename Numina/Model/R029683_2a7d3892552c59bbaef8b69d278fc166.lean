import Mathlib

theorem number_theory_230369 (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (hpa : ¬p ∣ a) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h : Fact (Nat.Prime p) := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card_sub_one_eq_one, ZMod.natCast_zmod_eq_zero_iff_dvd, show ¬p ∣ a by exact hpa]