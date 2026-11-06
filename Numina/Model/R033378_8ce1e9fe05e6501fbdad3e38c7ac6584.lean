import Mathlib

theorem number_theory_162234 (k : ℕ) (hk : 0 < k) :
    ∃ n, ∀ m ∈ Finset.range k, ¬Nat.Prime (n + m) := by
  use (k + 1).factorial + 2
  intro m hm
  rw [Finset.mem_range] at hm
  have h1 : m < k := by
    simpa using hm
  have h2 : m ≤ k - 1 := by
    omega
  have h3 : 2 + m ≤ k + 1 := by 
    omega
  have h5 : 2 + m ∣ (k + 1).factorial := by
    apply Nat.dvd_factorial
    all_goals
    omega
  have h6 : 2 + m ∣ ((k + 1).factorial + 2 + m) := by 
    have h7 : 2 + m ∣ (k + 1).factorial := h5
    have h8 : 2 + m ∣ (2 + m : ℕ) := by
      simp
    have h9 : 2 + m ∣ ((k + 1).factorial + (2 + m)) := by 
      apply Nat.dvd_add
      exact h7
      exact h8
    have h10 : ((k + 1).factorial + 2 + m) = ((k + 1).factorial + (2 + m)) := by 
      ring
    rw [h10]
    exact h9
  -- Show that (k+1)! + 2 + m is not prime by showing it has a non-trivial divisor.
  have h7 : ¬Nat.Prime ((k + 1).factorial + 2 + m) := by
    apply Nat.not_prime_of_dvd_of_lt h6
    all_goals
    have h8 : (2 + m) > 1 := by
      omega
    have h9 : (2 + m) < (k + 1).factorial + 2 + m := by 
      have h10 : (k + 1).factorial > 0 := by
        apply Nat.factorial_pos
      nlinarith
    all_goals
      omega
  simpa using h7