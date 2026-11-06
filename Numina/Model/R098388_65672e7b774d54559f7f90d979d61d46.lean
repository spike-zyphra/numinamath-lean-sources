import Mathlib

theorem number_theory_4927_1 (n p: ℕ) (_ : 0 < n) [hp1 : Fact (Nat.Prime p)] (hp2 : p = 2 * n + 1) :
    p ∣ mersenne n ∨ p ∣ mersenne n + 2 := by
  --we prove that if n is a positive integer and 2n+1 is prime then 2n+1 divides Mn or Mn+2
  --use the property of prime numbers and show that we only need to prove p divides the product Mn(Mn+2)
  have r0 := Nat.prime_iff.mp hp1.1
  rw [Prime] at r0
  apply r0.right.right; rw [mersenne]
  --simplify Mn(Mn+2) to 2 ^ (2n) - 1
  have r2 : (2 ^ n - 1) * (2 ^ n - 1 + 2) = 2 ^ (2 * n) - 1 := by
    rw [← Nat.sub_add_comm, mul_comm]; simp; rw [← Nat.sq_sub_sq, pow_two]
    ring_nf; exact Nat.one_le_pow n 2 (show 0 < 2 from by norm_num)
  rw [r2]
  --prepare to use Fermat's little theorem then apply the theorem
  have r3 : Odd p := ⟨n, hp2⟩
  have r4 : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have r5 : (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr r3)) ^ (p - 1) = 1 := by
    rw [← r4]; apply pow_card_eq_one
  apply Units.eq_iff.mpr at r5
  rw [Units.val_pow_eq_pow_val] at r5
  have r6 : Units.val (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr r3)) = 2 := rfl
  have r7 : Units.val (1 : (ZMod p)ˣ) = 1 := rfl
  rw [r6, r7] at r5; simp only [hp2] at r5; simp at r5
  rw [← sub_eq_zero] at r5
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (2 * n) - 1) p).mp; simp; exact r5

theorem number_theory_4927_2 : ¬ Nat.Prime (mersenne 11) := by
  --we show that M11 is composite by proving that 23 divides M11
  have : mersenne 11 = 2047 := by
    rw [mersenne]; norm_num
  rw [Nat.prime_def_lt]; push_neg; intro _; use 23
  rw [this]; constructor; norm_num; constructor; norm_num; norm_num

theorem number_theory_4927_3 : ¬ Nat.Prime (mersenne 23) := by
  --we show that M23 is composite by proving that 47 divides M23
  have : mersenne 23 = 8388607 := by
    rw [mersenne]; norm_num
  rw [Nat.prime_def_lt]; push_neg; intro _; use 47
  rw [this]; constructor; norm_num; constructor; norm_num; norm_num