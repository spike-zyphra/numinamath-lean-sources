import Mathlib


theorem number_theory_95961 (n : ℕ) (hn : 1 < n) :
    {p | p.Prime ∧ p > Nat.factorial n + 1 ∧ p < Nat.factorial n + n}.encard = 0 := by
  have h1 : {p | p.Prime ∧ p > Nat.factorial n + 1 ∧ p < Nat.factorial n + n} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hp
    rcases hp with ⟨h_prime, hp1, hp2⟩
    have h4 : p < Nat.factorial n + n := by
      linarith
    have h13 : ∃ k : ℕ, p = Nat.factorial n + k ∧ 2 ≤ k ∧ k < n := by
      use p - Nat.factorial n
      constructor
      · -- Show p = n! + k
        omega
      constructor
      · -- Show 2 ≤ k
        by_contra h
        push_neg at h
        have h17 : p - Nat.factorial n < 2 := by
          omega
        have h18 : p ≤ Nat.factorial n + 1 := by
          omega
        omega
      · -- Show k < n
        by_contra h
        push_neg at h
        have h19 : p - Nat.factorial n ≥ n := by
          omega
        have h20 : p ≥ Nat.factorial n + n := by
          omega
        omega
    rcases h13 with ⟨k, hp_eq, hk1, hk2⟩
    have h100 : ¬p.Prime := by
      rw [hp_eq]
      have hk3 : 2 ≤ k := by linarith
      have hk4 : k < n := by linarith
      have hk5 : k ∣ (Nat.factorial n + k : ℕ) := by
        have hk6 : k ∣ Nat.factorial n := by
          apply Nat.dvd_factorial
          all_goals
            omega
        have hk8 : k ∣ (k : ℕ) := by
          exact dvd_refl k
        have h12 : k ∣ (Nat.factorial n + k : ℕ) := by
          apply Nat.dvd_add hk6 hk8
        exact h12
      have hk8 : k < (Nat.factorial n + k : ℕ) := by
        have hk9 : Nat.factorial n > 0 := by
          apply Nat.factorial_pos
        have hk10 : k > 0 := by
          omega
        omega
      have hk9 : k > 1 := by
        omega
      have hk10 : ¬ (Nat.factorial n + k).Prime := by
        apply Nat.not_prime_of_dvd_of_lt hk5
        all_goals
          omega
      tauto
    contradiction
  rw [h1]
  simp