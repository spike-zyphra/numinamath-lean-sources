import Mathlib

/- Theorem 8.1 states that if \( a \) and \( n \) are relatively prime integers with \( n > 0 \), then a positive integer \( x \) is a solution to the congruence \( a^{x} \equiv 1 \mod n \) if and only if the order of \( a \) modulo \( n \), denoted as \( \operatorname{ord}_{n} a \), divides \( x \).-/
theorem number_theory_4983 (a n x: ℕ) (_ : NeZero n) (han : Nat.Coprime a n) :
    a ^ x ≡ 1 [MOD n] ↔ orderOf (ZMod.unitOfCoprime a han) ∣ x := by
  --we prove that if a and n are relatively prime, then a^x=1 mod n if and only if ord a divides x
  --prepare to rewrite the modulo equation to group identities in the unit group of (ZMod n)
  have r0 : Units.val (1 : (ZMod n)ˣ) = 1 := rfl
  have r1 : Units.val (ZMod.unitOfCoprime a han) = a := rfl
  constructor
  --apply the lemma orderOf_dvd_iff_pow_eq_one and prove the result
  · intro heq
    apply (ZMod.eq_iff_modEq_nat n).mpr at heq; simp at heq
    rw [← r1, ← r0, ← Units.val_pow_eq_pow_val, Units.eq_iff] at heq
    rw [orderOf_dvd_iff_pow_eq_one]; exact heq
  intro hdvd
  rw [orderOf_dvd_iff_pow_eq_one] at hdvd
  apply (ZMod.eq_iff_modEq_nat n).mp; simp
  rw [← r1, ← r0, ← Units.val_pow_eq_pow_val, Units.eq_iff]; exact hdvd
