import Mathlib

open Nat

theorem number_theory_236821 {p a : ℕ} (hp : Nat.Prime p) (hpa : ¬p ∣ a) :
    a^(p-1) ≡ 1 [MOD p] := by
  have h1 : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card_sub_one_eq_one, ZMod.nat_cast_zmod_eq_zero_iff_dvd, hpa]