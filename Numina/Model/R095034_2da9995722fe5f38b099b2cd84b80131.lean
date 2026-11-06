import Mathlib

theorem number_theory_7825
(a b p : ℕ)
(h₀ : Nat.Prime p)
(h₁ : p ∣ a * b) :
p ∣ a ∨ p ∣ b := by 
  exact (Nat.Prime.dvd_mul h₀).mp h₁