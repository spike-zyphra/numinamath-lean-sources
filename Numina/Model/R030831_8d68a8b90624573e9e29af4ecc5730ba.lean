import Mathlib
open Nat

theorem number_theory_8041 (n : ℕ) (hn : 1 < n) :
    ∃ m : ℕ, ∀ j ∈ Finset.range n, ¬Nat.Prime (m + j) := by
  use (n + 1).factorial + 2
  intro j hj
  have h1 : j < n := by
    simp [Finset.mem_range] at hj
    linarith
  have h3 : j + 2 ≤ n + 1 := by
    omega
  have h4 : j + 2 ∣ (n + 1).factorial := by 
    apply Nat.dvd_factorial
    all_goals 
      omega
  have h6 : (j + 2) ∣ ((n + 1).factorial + (j + 2 : ℕ)) := by 
    have h7 : (j + 2) ∣ ((n + 1).factorial) := h4 
    have h8 : (j + 2) ∣ (j + 2 : ℕ) := by 
      simp 
    have h9 : (j + 2) ∣ ((n + 1).factorial + (j + 2 : ℕ)) := by 
      apply Nat.dvd_add 
      exact h7 
      exact h8 
    exact h9 
  have h7 : ¬ Nat.Prime ((n + 1).factorial + (j + 2)) := by 
    apply Nat.not_prime_of_dvd_of_lt h6
    all_goals
      have h8 : j + 2 ≥ 2 := by
        omega
      have h9 : ( (n + 1).factorial + (j + 2) ) > (j + 2 : ℕ) := by
        have h10 : (n + 1).factorial ≥ 1 := by 
          apply Nat.factorial_pos
        have h11 : (n + 1).factorial + (j + 2) > (j + 2 : ℕ) := by 
          linarith [h10]
        linarith 
      all_goals
        omega 
  have h8 : ( (n + 1).factorial + 2 + j ) = ( (n + 1).factorial + (j + 2 : ℕ) ) := by 
    omega 
  rw [h8] 
  exact h7