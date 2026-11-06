import Mathlib

/- prepare the instance that 2 is a unit in ZMod p -/
instance inst2 (p : ℕ)(hp2 : Odd p) : OfNat (ZMod p)ˣ 2 :=
  OfNat.mk (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hp2))

/- 14. Let \( p \) be a prime divisor of the Fermat number \( F_n = 2^{2^n} + 1 \).
a) Show that the order of 2 modulo \( p \), denoted \( \operatorname{ord}_{p} 2 \), is equal to \( 2^{n+1} \).
b) From part (a), conclude that \( 2^{n+1} \) divides \( (p-1) \), so that \( p \) must be of the form \( 2^{n+1} k + 1 \) for some integer \( k \).-/
theorem number_theory_5005 (n p F: ℕ) [hp : Fact (Nat.Prime p)] (h'p : Odd p)
    (hF : F = 2 ^ 2 ^ n + 1) (pdF : p ∣ F) :
    orderOf (inst2 p h'p).1 = 2 ^ (n + 1) ∧ 2 ^ (n + 1) ∣ (p - 1) := by
  --prepare to rewrite congruence equations to group identities in the unit group of ZMod p
  have r1 := ZMod.card_units p
  have r2 : Units.val (inst2 p h'p).1 = 2 := rfl
  have r3 : Units.val (-1 : (ZMod p)ˣ) = -1 := rfl
  have r4 : Units.val (1 : (ZMod p)ˣ) = 1 := rfl
  have r5 := (Nat.prime_def_lt.mp hp.1).left
  --rewrite the condition that p divides F to a group identity
  rw [hF] at pdF; apply Nat.modEq_zero_iff_dvd.mpr at pdF
  apply (ZMod.eq_iff_modEq_nat p).mpr at pdF; simp at pdF
  apply add_eq_zero_iff_eq_neg.mp at pdF
  rw [← r2, ← r3, ← Units.val_pow_eq_pow_val] at pdF
  apply Units.eq_iff.mp at pdF
  have r6 : (inst2 p h'p).1 ^ 2 ^ (n + 1) = 1 := by
    rw [pow_add, pow_mul, pow_one, pow_two, pdF]; simp
  --apply the lemma orderOf_dvd_iff_pow_eq_one and prepare to use the lemma Nat.eq_prime_pow_of_dvd_least_prime_pow
  have t1 := orderOf_dvd_iff_pow_eq_one.mpr r6
  have t2 : ¬ orderOf (inst2 p h'p).1 ∣ 2 ^ n := by
    intro hneg; rw [orderOf_dvd_iff_pow_eq_one] at hneg
    rw [pdF] at hneg; apply Units.eq_iff.mpr at hneg
    rw [r3, r4] at hneg
    have : ZMod.val ((-1) : (ZMod p)) = 1 := by
      rw [hneg]; exact ZMod.val_one p
    rw [ZMod.val_neg_of_ne_zero 1, ZMod.val_one p, Nat.sub_eq_iff_eq_add] at this
    simp at this; rw [this] at h'p; contradiction; linarith
  have t3 := Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two t2 t1
  constructor; exact t3
  rw [← t3, symm r1]; exact orderOf_dvd_card
