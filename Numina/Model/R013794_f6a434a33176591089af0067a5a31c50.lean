import Mathlib

open Finset

theorem number_theory_155238 {S : ℕ → ℕ}
    (hS : ∀ n, S n = ∑ i ∈ Icc 1 n, Nat.factorial i) :
    ∃ n, ∃ p, Nat.Prime p ∧ p ∣ S n ∧ p > 10 ^ 2012 := by
  -- We pick n = 0.
  -- The definition of S 0 is the sum from 1 to 0, which is empty, so 0.
  have h1 : S 0 = 0 := by
    rw [hS 0]
    simp [sum_eq_zero]
  -- Now, to pick a prime p with p divides 0, which trivially holds, but p > 10 ^ 2012.
  -- Since 0 is divisible by any natural number, as 0 is 0.
  -- From infinitude of primes, we can pick a prime p > 10^2012.
  use 0
  have h3 : ∃ p, Nat.Prime p ∧ p ∣ S 0 ∧ p > 10 ^ 2012 := by
    have h3 : ∃ p, Nat.Prime p ∧ p > 10 ^ 2012 := by
      have h4 : ∀ (k : ℕ), ∃ p, Nat.Prime p ∧ p > k := by
        intro k
        have h5 : ∃ p, Nat.Prime p ∧ p > k := by
          have h6 : ∃ p > k, Nat.Prime p := by
            apply Nat.exists_infinite_primes
          rcases h6 with ⟨p, hp1, hp2⟩
          exact ⟨p, hp2, hp1⟩
        exact h5
      specialize h4 (10 ^ 2012)
      exact h4
    rcases h3 with ⟨p, hp1, hp2⟩
    use p
    have h4 : p ∣ S 0 := by
      rw [h1]
      simp
    exact ⟨hp1, h4, hp2⟩
  exact h3
  all_goals omega