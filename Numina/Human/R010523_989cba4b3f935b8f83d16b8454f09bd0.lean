import Mathlib

open Nat

/-
Proposition 3.4 states that for a prime number \( p \), a positive integer \( a \) is its own inverse modulo \( p \) if and only if \( a \equiv 1 \mod p \) or \( a \equiv -1 \mod p \).
-/
theorem number_theory_4684 (p a : ℕ) (hp : Nat.Prime p) (ha : 0 < a) :
                           a * a ≡ 1 [MOD p] ↔ a ≡ 1 [MOD p] ∨ a ≡ -1 [ZMOD p] := by
  -- We need to prove the entire statement in both directions.
  constructor <;> intro h
  · -- First, assume \( a * a \equiv 1 \mod p \), we need to prove \( a \equiv 1 \mod p \) or \( a \equiv -1 \mod p \).
    -- According to the assumption, we have \( a * a - 1 + 1 \equiv 0 + 1 \mod p \).
    have : a * a - 1 + 1 ≡ 0 + 1 [MOD p] := by
      have : a * a = a * a - 1 + 1 := by
        rw [Nat.sub_add_cancel]
        nlinarith
      rw [this] at h
      nth_rw 3 [(show 1 = 0 + 1 by ring_nf)] at h
      exact h
    -- That is, \( a * a - 1 \equiv 0 \mod p \).
    have := Nat.ModEq.add_right_cancel' 1 this
    -- Therefore, \( (a * a - 1) \% p = 0 \).
    dsimp [Nat.ModEq] at this
    simp at this
    -- Clearly, \( a * a - 1 = (a + 1)(a - 1) \).
    have t : a * a - 1 = (a + 1) * (a - 1) := by
      rw [(show 1 = 1^2 by ring_nf), (show a * a = a^2 by ring)]
      exact Nat.pow_two_sub_pow_two a 1
    -- Therefore, \( (a + 1)(a - 1) \% p = 0 \).
    rw [t] at this
    -- Thus, \( p \mid (a + 1)(a - 1) \).
    have : p ∣ (a + 1) * (a - 1) := Nat.dvd_of_mod_eq_zero this
    -- Since \( p \) is prime, we have \( p \mid a + 1 \) or \( p \mid a - 1 \).
    have := (Nat.Prime.dvd_mul hp).mp this
    -- We will discuss this case by case.
    cases this with
    | inl h' =>
      -- If \( p \mid a + 1 \), then \( a + 1 \equiv 0 \mod p \), so \( a \equiv -1 \mod p \).
      right
      have h' : (p : ℤ) ∣ (a : ℤ) + 1 := by norm_cast
      rw [(show (a : ℤ) + 1 = a - (-1) by ring)] at h'
      exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr h')
    | inr h' =>
      -- If \( p \mid a - 1 \), then \( a - 1 \equiv 0 \mod p \), so \( a \equiv 1 \mod p \).
      left
      have h' : (p : ℤ) ∣ (a : ℤ) - 1 := by
        have : 1 ≤ a := by nlinarith
        norm_cast
      exact Nat.ModEq.symm (Nat.modEq_iff_dvd.mpr h')
  · -- Next, we prove in the other direction.
    -- First, we assume \( a \equiv -1 \mod p \) or \( a \equiv 1 \mod p \).
    -- We will discuss this case by case.
    cases h with
    | inl h =>
      -- If \( a \equiv 1 \mod p \), then \( a * a \equiv 1 \mod p \) obviously holds.
      rw [(show 1 = 1 * 1 by ring)]
      exact Nat.ModEq.mul h h
    | inr h =>
      -- Similarly, if \( a \equiv -1 \mod p \), then \( a * a \equiv 1 \mod p \) holds.
      suffices h' : (a : ℤ) * a ≡ 1 [ZMOD p] from by
        exact Int.natCast_modEq_iff.mp h'
      rw [(show 1 = -1 * -1 by ring)]
      exact Int.ModEq.mul h h
  -- Thus, the proof of the original statement is complete.
