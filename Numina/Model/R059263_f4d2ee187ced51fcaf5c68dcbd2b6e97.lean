import Mathlib

open Nat

theorem number_theory_295835 {p : ℕ} (hp : 2 ≤ p) :
    Nat.Prime p ↔ ((p - 1)! : ZMod p) = -1 := by
  apply Iff.intro
  · -- Assume p is prime, we need to prove (p - 1)! = -1 in ZMod p
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mp
    exact h
  · -- Assume (p - 1)! = -1 in ZMod p, we need to prove p is prime
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mpr
    exact h