import Mathlib

theorem number_theory_190847 : 3 ∣ (2 ^ (2 ^ 1959) - 1) := by
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat]
  native_decide