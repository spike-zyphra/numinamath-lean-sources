import Mathlib

theorem number_theory_165113 (n : ℕ) (hn : n > 0) (h3 : 3 ∣ n) (h5 : 5 ∣ 3 * n) :
    n ≥ 15 := by 
  have h5n : 5 ∣ n := by 
    have h : 5 ∣ 3 * n := h5
    have : 5 ∣ n := by 
      omega
    exact this
  have h15 : 15 ∣ n := by
    have h3n : 3 ∣ n := h3
    have h5n' : 5 ∣ n := h5n
    have h15n : 15 ∣ n := by
      omega
    exact h15n
  have : n ≥ 15 := by
    apply Nat.le_of_dvd (by omega) h15
  linarith