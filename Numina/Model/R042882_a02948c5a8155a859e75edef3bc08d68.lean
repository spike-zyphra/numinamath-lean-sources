import Mathlib


theorem algebra_284536 (n : ℕ) (hn : n > 0) :
    ¬(n^2 + 8 * n + 15) % (n + 4) = 0 := by 
  by_contra h
  have h1 : (n + 4) ∣ (n^2 + 8 * n + 15) := by
    have h2 : (n ^ 2 + 8 * n + 15) % (n + 4) = 0 := by
      simpa using h
    exact Nat.dvd_of_mod_eq_zero h2

  have h4 : (n + 4) ∣ (1 : ℕ) := by
    have h3 : (n + 4) ∣ ((n + 4) ^ 2 : ℕ) := by
      use (n + 4)
      all_goals ring_nf
    have h7 : (n + 4) ∣ (( (n + 4) ^ 2 ) - (n^2 + 8 * n + 15) : ℕ) := by
      apply Nat.dvd_sub'
      · exact h3
      · exact h1
    have h8 : (( (n + 4) ^ 2 ) - (n^2 + 8 * n + 15) : ℕ) = 1 := by
      ring_nf
      <;> omega
    rw [h8] at h7
    exact h7

  have h5 : (n + 4) ≤ (1 : ℕ) := by
    exact Nat.le_of_dvd (by linarith) h4

  have h6 : n + 4 > (1 : ℕ) := by
    omega
  linarith