import Mathlib

open Nat

/- Show that there are infinitely many prime numbers whose last digit is not 1 . -/
theorem number_theory_259153 : Set.Infinite {p : ℕ | p.Prime ∧ p % 10 ≠ 1} := by
  -- By Dirichlet's theorem, there are infinitely many primes of the form 10k + 9.
  have H := Nat.setOf_prime_and_eq_mod_infinite (q := 10) (a := 9) (by decide)
  -- There are more primes that are not of the form 10k + 1 than there are of the form 10k + 9.
  refine H.mono ?_
  intro p ⟨hp₁, hp₂⟩
  refine ⟨hp₁, ?_⟩
  change (p : ZMod 10) = (9 : ℕ) at hp₂
  rw [ZMod.natCast_eq_natCast_iff'] at hp₂
  simp [hp₂]
