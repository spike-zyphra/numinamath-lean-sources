import Mathlib

theorem number_theory_173605 (p : ℕ) (hp : Nat.Prime p) (h : p > 3) :
    ∃ n : ℕ, n ≠ 0 ∧ p = 6 * n + 1 ∨ p = 6 * n - 1 := by
  have h1 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have h3 : p % 2 = 0 := by omega
    have h4 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    tauto
  have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h3
    push_neg at h3
    have h4 : p % 3 = 0 := by omega
    have h6 : p > 3 := h
    have h4' : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    tauto
  have h3 : p % 6 = 1 ∨ p % 6 = 5 := by 
    omega
  rcases h3 with (h3 | h3)
  · -- Case p % 6 = 1
    use p / 6
    have h4 : p = 6 * (p / 6) + 1 := by 
      omega
    have hp5 : p / 6 ≠ 0 := by
      omega
    left
    constructor 
    · exact hp5 
    · exact h4
  · -- Case p % 6 = 5
    use p / 6 + 1
    have h4 : p = 6 * (p / 6 + 1) - 1 := by 
      omega
    right
    exact h4