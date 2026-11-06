import Mathlib

theorem number_theory_123288 (n : ℕ) (hn : n > 0) :
    ∃ k, ∀ i ∈ Finset.range n, ¬Nat.Prime (k + i) := by
  use (n + 1).factorial + 2
  intro i hi
  have h1 : i < n := by 
    simp [Finset.mem_range] at hi
    omega
  have h2 : i + 2 ≤ n + 1 := by
    omega
  have h3 : (i + 2) ∣ ((n + 1).factorial + 2 + i) := by
    have h4 : (i + 2) ∣ (n + 1).factorial := by
      apply Nat.dvd_factorial
      all_goals
        omega
    have h5 : (i + 2) ∣ ( (n + 1).factorial + 2 + i ) := by
      have h7 : (i + 2) ∣ ( (n + 1).factorial ) := h4
      have h8 : (i + 2) ∣ (i + 2) := by
        apply dvd_refl
      have h9 : (i + 2) ∣ ( (n + 1).factorial + (i + 2) ) := by
        apply Nat.dvd_add
        exact h7
        exact h8
      have h10 : ( (n + 1).factorial + 2 + i ) = ( (n + 1).factorial + (i + 2) ) := by
        omega
      rw [h10]
      exact h9
    exact h5
  have h4 : ¬Nat.Prime ((n + 1).factorial + 2 + i) := by
    apply Nat.not_prime_of_dvd_of_lt h3
    all_goals
      have h5 : (n + 1).factorial > 0 := by
        apply Nat.factorial_pos
      nlinarith
  simpa using h4