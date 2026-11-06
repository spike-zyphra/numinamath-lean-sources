import Mathlib

open Nat

theorem number_theory_107281 {p : ℕ} (hp : 1 < p) :
    Nat.Prime p ↔ ((p - 1)! : ZMod p) = -1 := by
  apply Iff.intro
  · -- Assume p is prime, prove (p - 1)! = -1 in ZMod p
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mp at h
    simpa using h
  · -- Assume (p - 1)! = -1 in ZMod p, prove p is prime
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mpr
    simpa using h