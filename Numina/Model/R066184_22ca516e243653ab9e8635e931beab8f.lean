import Mathlib

theorem number_theory_188787 {n : ℕ} (hn : n > 0) (h : (n / 10) * 9 = n) :
    ∃ k, (n / 10 ^ k) % 10 = 0 := by 
  have h1 : n = 0 := by 
    omega 
  linarith