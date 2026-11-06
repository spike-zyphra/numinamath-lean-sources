import Mathlib

open Nat

theorem number_theory_102040 {p : ℕ} (hp : 1 < p) :
    p.Prime ↔ ((p - 1)! : ZMod p) = -1 := by 
  apply Iff.intro
  · -- Assume p is prime, prove (p - 1)! ≡ -1 (mod p)
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mp
    exact h
  · -- Assume (p - 1)! ≡ -1 (mod p), prove p is prime
    intro h
    apply (Nat.prime_iff_fac_equiv_neg_one (by linarith)).mpr
    exact h