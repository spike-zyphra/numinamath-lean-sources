import Mathlib

/- Show that if \( a \) and \( b \) are positive integers and \( p \) is a prime number such that \( p \) does not divide \( a \), then the solutions to the linear congruence \( a x \equiv b \mod p \) are the integers \( x \) that satisfy \( x \equiv a^{p-2} b \mod p \).-/
theorem number_theory_4780 {a b p x : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) (haxb : a*x ≡ b [MOD p]) :
    x ≡ a^(p-2)*b [MOD p] := by
  -- Since \( p \) does not divide \( a \), we can apply Theorem 5.2, which tells us that \( a^{p-2} \) is the modular inverse of \( a \) modulo \( p \).
  haveI := Nat.Prime.two_le hp
  haveI := Fact.mk hp
  have ha : (a : ZMod p) ≠ 0 := fun h => by
    rw [show (0 : ZMod p) = Nat.cast 0 by norm_cast, ZMod.eq_iff_modEq_nat, Nat.modEq_zero_iff_dvd] at h
    contradiction
  have hfermat := ZMod.pow_card_sub_one_eq_one ha
  push_cast at hfermat
  rw [show p - 1 = p - 2 + 1 by omega, pow_succ] at hfermat
  rw [← ZMod.eq_iff_modEq_nat] at haxb ⊢
  push_cast at haxb ⊢
  -- Now, we multiply both sides of the original congruence \( a x \equiv b \mod p \) by \( a^{p-2} \):
-- \[
-- a^{p-2} a x \equiv a^{p-2} b \mod p
-- \]
  apply_fun ((a : ZMod p)^(p - 2) * ·) at haxb
--   On the left side, since \( a^{p-2} \) is the inverse of \( a \), we simplify \( a^{p-2} a \) to 1:
-- \[
-- 1 \cdot x \equiv a^{p-2} b \mod p
-- \]
-- This simplifies to:
-- \[
-- x \equiv a^{p-2} b \mod p
-- \]
  rwa [← mul_assoc, hfermat, one_mul] at haxb
