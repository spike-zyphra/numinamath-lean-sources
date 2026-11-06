import Mathlib

theorem number_theory_217834 (n : ℕ) (h : n > 0) :
    (n + 1) ∣ Nat.factorial n + 1 → Nat.Prime (n + 1) := by
  intro h1
  by_contra h2
  have h3 : ¬ Nat.Prime (n + 1) := h2
  have h4 : n + 1 > 1 := by linarith
  have h5 : ∃ m, m ∣ n + 1 ∧ 1 < m ∧ m < n + 1 := by
    have h5 : ¬ Nat.Prime (n + 1) := h3
    rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)] at h5
    tauto
  rcases h5 with ⟨m, hm1, hm2, hm3⟩
  have h6 : m ≤ n := by 
    omega
  have h7 : m ∣ Nat.factorial n := by
    apply Nat.dvd_factorial
    all_goals
      omega
  have h8 : m ∣ Nat.factorial n + 1 := by
    have h9 : m ∣ n + 1 := hm1
    have h10 : n + 1 ∣ Nat.factorial n + 1 := h1
    exact dvd_trans h9 h10
  have h9 : m ∣ 1 := by
    have h10 : m ∣ Nat.factorial n := h7
    have h11 : m ∣ Nat.factorial n + 1 := h8
    have h12 : m ∣ (Nat.factorial n + 1 - Nat.factorial n) := by
      apply Nat.dvd_sub'
      · exact h11
      · exact h10
    have h13 : Nat.factorial n + 1 - Nat.factorial n = 1 := by 
      omega
    rw [h13] at h12
    exact h12
  have h10 : m ≤ 1 := by 
    exact Nat.le_of_dvd (by linarith) h9
  omega