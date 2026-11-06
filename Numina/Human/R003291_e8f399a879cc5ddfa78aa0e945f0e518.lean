import Mathlib

theorem number_theory_167159 (n : ℕ) (h₀ : n > 0) :
    ∃ k, n + (Nat.digits 10 n).sum * k = n := by 
  use 0 
  simp