import Mathlib

theorem number_theory_246884 {n : ℕ} (hn : n % 5 = 0 ∧ n % 7 = 0 ∧ n % 9 = 0)
    (h : n / 5 + n / 7 + n / 9 = 286) : n = 630 := by 
  rcases hn with ⟨h5, h7, h9⟩
  have h315 : n % 315 = 0 := by
    omega
  have : n = 630 := by 
    omega
  exact this