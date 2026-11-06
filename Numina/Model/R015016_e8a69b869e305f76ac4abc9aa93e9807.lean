import Mathlib


lemma lemma_1 (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ n + 1) :
    ¬ Nat.Prime (Nat.factorial (n + 1) + k) := by
  rcases hk with ⟨hk1, hk2⟩
  have h1 : k ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial
    all_goals
    omega
  have h2 : k ∣ (Nat.factorial (n + 1) + k) := by
    have h3 : k ∣ Nat.factorial (n + 1) := h1
    have h4 : k ∣ k := by
      simp
    apply Nat.dvd_add
    .
      exact h3
    .
      exact h4
  have h3 : ¬ Nat.Prime (Nat.factorial (n + 1) + k) := by
    apply Nat.not_prime_of_dvd_of_lt h2
    all_goals
    have h4 : k > 1 := by omega
    have h5 : Nat.factorial (n + 1) + k > k := by
      have h2 : Nat.factorial (n + 1) > 0 := by
        apply Nat.factorial_pos
      omega
    all_goals
    omega
  exact h3


theorem number_theory_144532 (n : ℕ) (hn : 1 < n) :
    ∃ k, ∀ i ∈ Finset.Icc k (k + n - 1), ¬Nat.Prime i := by
  use Nat.factorial (n + 1) + 2
  intro i hi
  rw [Finset.mem_Icc] at hi
  rcases hi with ⟨h1, h2⟩
  have h3 : i ≤ Nat.factorial (n + 1) + n + 1 := by
    omega
  have h4 : i = Nat.factorial (n + 1) + (i - Nat.factorial (n + 1)) := by
    omega
  have h5 : 2 ≤ i - Nat.factorial (n + 1) := by
    omega
  have h6 : i - Nat.factorial (n + 1) ≤ n + 1 := by
    omega
  rw [h4]
  apply lemma_1 n (by linarith) (i - Nat.factorial (n + 1)) ⟨by omega, by omega⟩