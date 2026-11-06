import Mathlib

/- Theorem 8.2 states that if \( a \) and \( n \) are relatively prime integers with \( n > 0 \), then \( a^{i} \equiv a^{j} \mod n \) for nonnegative integers \( i \) and \( j \) if and only if \( i \equiv j \mod \operatorname{ord}_{n} a \).-/
theorem number_theory_4985 (a n i j: ℕ) (_ : NeZero n) (han : Nat.Coprime a n) :
    a ^ i ≡ a ^ j [MOD n] ↔ i ≡ j [MOD orderOf (ZMod.unitOfCoprime a han)] := by
  --The problem is exactly the proposition pow_eq_pow_iff_modEq in Mathlib.
  have r1 : Units.val (ZMod.unitOfCoprime a han) = a := rfl
  constructor
  · intro hij; apply (ZMod.eq_iff_modEq_nat n).mpr at hij; simp at hij
    rw [← r1, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.eq_iff, pow_eq_pow_iff_modEq] at hij
    exact hij
  intro h'ij; apply (ZMod.eq_iff_modEq_nat n).mp; simp
  rw [← r1, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.eq_iff, pow_eq_pow_iff_modEq]
  exact h'ij
