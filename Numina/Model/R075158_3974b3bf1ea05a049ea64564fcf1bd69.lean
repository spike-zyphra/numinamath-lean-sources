import Mathlib

theorem number_theory_8122
    (p a : ℕ)
    (h : p.Prime) :
    a^p ≡ a [MOD p] := by
  have h1 : Fact p.Prime := ⟨h⟩
  rw [← ZMod.eq_iff_modEq_nat p]
  simp [ZMod.pow_card]