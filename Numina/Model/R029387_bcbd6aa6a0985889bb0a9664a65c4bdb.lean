import Mathlib

theorem number_theory_4777 (p a : ℕ) (hp : Nat.Prime p) (_ : 0 < a) :
    a^p ≡ a [MOD p] := by
  have h₁ : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.eq_iff_modEq_nat]
  simp [ZMod.pow_card]