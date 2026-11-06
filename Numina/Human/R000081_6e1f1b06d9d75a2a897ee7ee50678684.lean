import Mathlib

open Nat

/- Show that for any positive integer \( n \), there exist at least \( n \) consecutive composite positive integers.-/
theorem number_theory_4483 (n : ℕ) (_ : n > 0) :
  ∃ k : ℕ, k ≥ 1 ∧ ∀ i : Finset.Icc k (k + n - 1), ¬ Nat.Prime i := by
--    To demonstrate this, we will consider the \( n \) consecutive positive integers given by the expressions:
-- $$(n+1)!+2, (n+1)!+3, \ldots, (n+1)!+n+1.$$
  use (n+1)! + 2
  have : 0 < (n+1)! := by apply Nat.factorial_pos
  constructor
  linarith
  simp
  intro a ha1 ha2
  -- This means that each of the integers \( (n+1)! + 2, (n+1)! + 3, \ldots, (n+1)! + (n+1) \) is divisible by \( j \) for its corresponding \( j \). Consequently, each of these integers is not prime, as they have divisors other than \( 1 \) and themselves.
  rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)]
  set k : ℕ := a - (n+1)! with hk
  use k
  have hak : a = (n+1)! + k := by
    rw [hk, ← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    . linarith
  refine ⟨?_, by linarith, by linarith⟩
  rw [hak]
--    By applying Proposition 1.4, we can conclude that since \( j \) divides \( (n+1)! \), it also divides \( (n+1)! + j \). Therefore, we have:
-- $$ j \mid ((n+1)! + j) \implies (n+1)! + j \equiv 0 \mod j. $$
  refine Nat.dvd_add ?_ (Nat.dvd_refl _)
  --  For each integer \( j \) in the range \( 2 \leq j \leq n+1 \), it is clear that \( j \) divides \( (n+1)! \) because \( (n+1)! \) is the factorial of \( n+1 \) and includes all integers from \( 1 \) to \( n+1 \) as factors.
  apply Nat.dvd_factorial
  linarith
  linarith
