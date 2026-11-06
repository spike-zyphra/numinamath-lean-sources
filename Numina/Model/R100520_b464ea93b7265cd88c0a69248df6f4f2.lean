import Mathlib

theorem number_theory_7053
    (p a : ℕ)
    (hp : Nat.Prime p)
    (hpa : ¬ p ∣ a) :
    a^(p - 1) ≡ 1 [MOD p] := by
  have h1 : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card_sub_one_eq_one, ZMod.natCast_zmod_eq_zero_iff_dvd, h1, hpa]