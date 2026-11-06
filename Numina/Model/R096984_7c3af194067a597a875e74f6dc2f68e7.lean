import Mathlib

theorem number_theory_110982 (a b n : ℕ) (h₀ : Nat.Coprime a b) (h₁ : a ∣ n) (h₂ : b ∣ n) :
    a * b ∣ n := by
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h₀ h₁ h₂