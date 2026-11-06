import Mathlib

/- Prove that $2^{2^{1989}}-1$ is divisible by 17. -/
theorem number_theory_218634 : 17 ∣ (2^(2^1989) - 1) := by
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat]
  -- Note that by Fermat's little theorem, we know that 2^16 ≡ 1 (mod 17).
  have h : 2^16 = (1 : ZMod 17) := by
    rw [show 16 = 17 - 1 by rfl]
    exact @ZMod.pow_card_sub_one_eq_one 17 (Fact.mk (by norm_num)) _ (by decide)
  -- Thus we can reduce the exponent modulo 16.
  have : 2^(2^1989) = ((2^16)^(2^1985) : ZMod 17) := by
    rw [← pow_mul, show 16 = 2^4 by norm_num, ← pow_add]
  rw [this, h, one_pow]
  simp