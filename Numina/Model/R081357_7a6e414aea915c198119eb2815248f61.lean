import Mathlib

open Nat

theorem number_theory_151603 {p : ℕ} (hp : 2 ≤ p) :
    Nat.Prime p ↔ ((p - 1) ! : ZMod p) = -1 := by
  apply Iff.intro
  · -- Forward: if p is prime, then (p - 1)! ≡ -1 (mod p)
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mp
    exact h
  · -- Backward: if (p - 1)! ≡ -1 (mod p), then p is prime
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mpr
    exact h