import Mathlib

theorem number_theory_233146 (a b c : ℕ) :
    2 ∣ a + b ∨ 2 ∣ a + c ∨ 2 ∣ b + c := by 
  have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega 
  have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega 
  have h3 : c % 2 = 0 ∨ c % 2 = 1 := by omega 
  omega