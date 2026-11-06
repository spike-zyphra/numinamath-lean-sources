import Mathlib

theorem number_theory_122648 (n : ℕ) :
    ∃ r : ℕ, ∀ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (r + k) := by
  use (n + 1).factorial + 1
  intro k hk
  rw [Finset.mem_Icc] at hk
  rcases hk with ⟨hk1, hkn⟩
  have h2 : k ≤ n := by linarith 
  have h3 : k + 1 ≤ n + 1 := by linarith 
  have h4 : (k + 1) ∣ (n + 1).factorial := by
    apply Nat.dvd_factorial
    all_goals linarith 
  have h5 : (k + 1) ∣ ((n + 1).factorial + (k + 1)) := by
    have h6 : (k + 1) ∣ (n + 1).factorial := h4
    have h7 : (k + 1) ∣ (k + 1) := by
      simp 
    apply Nat.dvd_add h4 h7
  have h7 : ((n + 1).factorial + 1 + k) = ((n + 1).factorial + (k + 1)) := by 
    omega 
  rw [h7] at *
  have h8 : ¬ Nat.Prime ((n + 1).factorial + (k + 1)) := by
    apply Nat.not_prime_of_dvd_of_lt h5
    all_goals
      have h8 : k ≥ 1 := by linarith 
      have h9 : (n + 1).factorial ≥ 1 := by
        have h10 : (n + 1) ≥ 1 := by linarith 
        have h11 : (n + 1).factorial ≥ 1 := by
          apply Nat.factorial_le h10
        exact h11 
      have h12 : (n + 1).factorial + (k + 1) ≥ 1 + (k + 1) := by
        linarith [h9] 
      have h13 : (n + 1).factorial + (k + 1) > (k + 1) := by 
        nlinarith 
      have h14 : k + 1 ≥ 2 := by 
        omega 
      all_goals 
        omega 
  exact h8