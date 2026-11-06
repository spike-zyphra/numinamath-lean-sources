import Mathlib

/- prepare the instance that if p is odd then 2 is a unit in ZMod p -/
instance inst (p : ℕ) (hp2 : Odd p) : OfNat (ZMod p)ˣ 2 :=
  OfNat.mk (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hp2))

/- 16. a) Show that if \( p \) and \( q \) are distinct odd primes, then \( pq \) is a pseudoprime to the base 2 if and only if \( \operatorname{ord}_{q} 2 \mid (p-1) \) and \( \operatorname{ord}_{p} 2 \mid (q-1) \).
b) Use part (a) to decide which of the following integers are pseudoprimes to the base 2: \( 13 \cdot 67, 19 \cdot 73, 23 \cdot 89, 29 \cdot 97 \).-/
theorem number_theory_5007 (p q : ℕ) (pnq : p ≠ q) [hp1 : Fact (Nat.Prime p)] (hp2 : Odd p)
    [hq1 : Fact (Nat.Prime q)] (hq2 : Odd q) :
    Nat.FermatPsp (p * q) 2 ↔
    orderOf (inst q hq2).1 ∣ (p - 1) ∧ orderOf (inst p hp2).1 ∣ (q - 1) := by
  --prepare some simple propositions for later use
  have r1 : Nat.Coprime p q := (Nat.coprime_primes hp1.1 hq1.1).mpr pnq
  have r2 : Nat.card (ZMod p)ˣ = p - 1 := by
    have := ZMod.card_units p
    rw [← Fintype.card_eq_nat_card]; exact this
  have r3 : Nat.card (ZMod q)ˣ = q - 1 := by
    have := ZMod.card_units q
    rw [← Fintype.card_eq_nat_card]; exact this
  --prove some identities that can be used for converting types
  have r4 : Units.val (inst q hq2).1 = 2 := rfl
  have r5 : Units.val (inst p hp2).1 = 2 := rfl
  have r6: (1 : ZMod q) = Units.val (1 : (ZMod q)ˣ) := rfl
  have r7: (1 : ZMod p) = Units.val (1 : (ZMod p)ˣ) := rfl
  have r9 := (Nat.prime_def_lt.mp hq1.1).left
  have r10 := (Nat.prime_def_lt.mp hp1.1).left
  have r8 : p * q - 1 - (p - 1) = p * (q - 1) := by
    rw [Nat.sub_sub, Nat.add_sub_cancel']; nth_rw 2 [← mul_one p]
    rw [Nat.mul_sub_left_distrib]; linarith
  have r11 : p * q - 1 - (q - 1) = q * (p - 1) := by
    rw [Nat.sub_sub, Nat.add_sub_cancel']; nth_rw 2 [← one_mul q]
    rw [Nat.mul_sub_left_distrib, mul_comm]; simp; linarith

  constructor
  --prove the "if" part of the proposition
  intro hpq; rw [Nat.FermatPsp] at hpq
  rcases hpq with ⟨hpq1, _, hpq3⟩; rw [Nat.probablePrime_iff_modEq] at hpq1
  apply (Nat.modEq_and_modEq_iff_modEq_mul r1).mpr at hpq1
  constructor
  · rw [orderOf_dvd_iff_pow_eq_one]
    have t1 := (ZMod.eq_iff_modEq_nat q).mpr hpq1.right
    simp at t1; rw [← r4, ← Units.val_pow_eq_pow_val, r6, Units.eq_iff] at t1
    rw [← t1, pow_eq_pow_iff_modEq, Nat.modEq_iff_dvd', r8]
    have : orderOf (inst q hq2).1 ∣ (q - 1) := by
      rw [← r3]; exact orderOf_dvd_natCard (inst q hq2).1
    rw [Nat.dvd_mul]; use 1; simp; exact this
    simp; rw [Nat.sub_add_cancel]; apply Nat.le_mul_of_pos_right
    linarith; linarith
  · rw [orderOf_dvd_iff_pow_eq_one]
    have t1 := (ZMod.eq_iff_modEq_nat p).mpr hpq1.left
    simp at t1; rw [← r5, ← Units.val_pow_eq_pow_val, r7, Units.eq_iff] at t1
    rw [← t1, pow_eq_pow_iff_modEq, Nat.modEq_iff_dvd', r11]
    have : orderOf (inst p hp2).1 ∣ (p - 1) := by
      rw [← r2]; exact orderOf_dvd_natCard (inst p hp2).1
    rw [Nat.dvd_mul]; use 1; simp; exact this
    simp; rw [Nat.sub_add_cancel]; apply Nat.le_mul_of_pos_left
    linarith; linarith
  norm_num

  --prove the "only if" part of the proposition
  rintro ⟨odp, odq⟩; rw [Nat.FermatPsp]; constructor
  rw [Nat.probablePrime_iff_modEq]; apply (Nat.modEq_and_modEq_iff_modEq_mul r1).mp
  constructor; apply (ZMod.eq_iff_modEq_nat p).mp; simp
  rw [← r5, r7, ← Units.val_pow_eq_pow_val, Units.eq_iff, pow_eq_one_iff_modEq]
  rw [Nat.modEq_zero_iff_dvd]
  rcases odq with ⟨w, hw⟩; rw [Nat.sub_eq_iff_eq_add] at hw
  rw [hw, mul_add, mul_one, Nat.add_sub_assoc, mul_comm, mul_assoc]
  apply Nat.dvd_add; exact Nat.dvd_mul_right (orderOf ((inst p hp2).1)) (w * p)
  rw [← r2]; exact orderOf_dvd_natCard (inst p hp2).1; linarith; linarith

  apply (ZMod.eq_iff_modEq_nat q).mp; simp
  rw [← r4, r6, ← Units.val_pow_eq_pow_val, Units.eq_iff, pow_eq_one_iff_modEq]
  rw [Nat.modEq_zero_iff_dvd]
  rcases odp with ⟨w, hw⟩; rw [Nat.sub_eq_iff_eq_add] at hw
  rw [hw, add_mul, one_mul, Nat.add_sub_assoc, mul_assoc]
  apply Nat.dvd_add; exact Nat.dvd_mul_right (orderOf ((inst q hq2).1)) (w * q)
  rw [← r3]; exact orderOf_dvd_natCard (inst q hq2).1; linarith; linarith

  norm_num; constructor; apply Nat.not_prime_mul; linarith; linarith;
  have : 2 * 2 ≤ p * q := Nat.mul_le_mul r10 r9
  simp at this; linarith
