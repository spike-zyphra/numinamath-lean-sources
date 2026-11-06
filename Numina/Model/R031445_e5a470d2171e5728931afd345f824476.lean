import Mathlib

theorem number_theory_4983 (a n x: ℕ) (_ : NeZero n) (han : Nat.Coprime a n) :
    a ^ x ≡ 1 [MOD n] ↔ orderOf (ZMod.unitOfCoprime a han) ∣ x := by
  rw [← ZMod.eq_iff_modEq_nat]
  simp [← Units.eq_iff, orderOf_dvd_iff_pow_eq_one]