import Mathlib

open Nat

/- Show that if \( n \) is a positive integer such that \( (n-1)! \equiv -1 \mod n \), then \( n \) must be a prime number.-/
theorem number_theory_4775 {n : ℕ} (hn : n ≠ 1) : n.Prime ↔ ((n - 1)! : ZMod n) = -1 :=
  -- exact `Nat.prime_iff_fac_equiv_neg_one` in Mathlib
  Nat.prime_iff_fac_equiv_neg_one hn
