import Mathlib

theorem number_theory_7419 (n : ℕ) :
    ∃ q > n, q.Prime ∧ ∃ m, m * (m + 1) % q = 0 := by
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (n + 1)
  use q
  constructor
  · -- Show that q > n
    linarith
  constructor
  · -- Show that q is prime
    exact hq2
  · -- Show that ∃ m, m * (m + 1) % q = 0
    use q
    simp [Nat.mul_mod, Nat.add_mod, Nat.mul_mod]