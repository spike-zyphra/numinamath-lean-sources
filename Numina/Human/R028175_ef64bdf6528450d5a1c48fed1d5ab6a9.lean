import Mathlib

/- Every positive integer greater than one has a prime divisor. -/
theorem number_theory_4479 {n : ℕ} (hn : 1 < n) : ∃ p, p.Prime ∧ p ∣ n := by
  -- use second mathematical induction
  induction' n using Nat.strongRecOn with n ih
  by_cases hnp : n.Prime
  -- if n is prime number, then n satisfies p | n
  . use n
  -- otherwise, there exists a | n such that a < n
  obtain ⟨a, ha⟩ := Nat.exists_dvd_of_not_prime2 hn hnp
  -- by induction hypothesis, there exists prime p | a
  obtain ⟨p, hp⟩ := ih a ha.2.2 ha.2.1
  -- p satisfies p | n
  use p
  constructor
  exact hp.1
  exact Nat.dvd_trans hp.2 ha.1
