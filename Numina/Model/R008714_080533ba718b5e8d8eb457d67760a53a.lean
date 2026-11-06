import Mathlib

theorem number_theory_4627
(a b c : ℤ)
(h₀ : a ∣ b)
(h₁ : b ∣ c) :
-- use the transitivity of divisibility。
a ∣ c := by 
  exact Int.dvd_trans h₀ h₁