import Mathlib

open Nat

/- Wilson's Theorem states that if \( p \) is a prime number, then \((p-1)! \equiv -1 \mod p\).-/
theorem number_theory_4774 (p : ℕ) [Fact p.Prime] : ((p-1)! : ZMod p) = -1 :=
  -- exact `ZMod.wilsons_lemma` in Mathlib
  ZMod.wilsons_lemma p
