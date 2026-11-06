import Mathlib

theorem number_theory_107265 (n : ℕ) :
    ∃ k, ∀ m ∈ Finset.range n, ¬Nat.Prime (k + m) := by 
  use (n + 1).factorial + 2
  intro m hm
  rw [Finset.mem_range] at hm
  have h1 : m < n := hm
  have h2 : m + 2 ≤ n + 1 := by omega
  have h3 : (m + 2) ∣ (n + 1).factorial := by
    apply Nat.dvd_factorial
    all_goals
      linarith
  have h5 : (m + 2) ∣ ((n + 1).factorial + (m + 2)) := by
    have h6 : (m + 2) ∣ (n + 1).factorial := h3
    have h7 : (m + 2) ∣ (m + 2) := by
      simp
    apply Nat.dvd_add h6 h7
  have h10 : ¬Nat.Prime ((n + 1).factorial + (m + 2)) := by
    apply Nat.not_prime_of_dvd_of_lt h5
    all_goals
      have h11 : m + 2 < (n + 1).factorial + (m + 2) := by
        have h12 : (n + 1).factorial > 0 := by
          apply Nat.factorial_pos
        omega
      omega
  have h11 : (n + 1).factorial + 2 + m = (n + 1).factorial + (m + 2) := by
    omega
  rw [show (n + 1).factorial + 2 + m = (n + 1).factorial + (m + 2) by omega]
  tauto