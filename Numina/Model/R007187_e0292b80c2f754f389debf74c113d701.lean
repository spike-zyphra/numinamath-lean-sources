import Mathlib

theorem number_theory_4746 (a b : ℕ) (_ : 0 < a) (h₁ : 0 < b) (h₂ : a ∣ b) : a ≤ b :=
  by 
    exact Nat.le_of_dvd (by linarith) h₂