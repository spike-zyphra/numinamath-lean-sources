import Mathlib

theorem algebra_8070 : ∀ a b c : ℤ, Even (a + b) ∨ Even (b + c) ∨ Even (a + c) := by 
  intro a b c 
  have h1 : a % 2 = 0 ∨ a % 2 = 1 := by 
    omega
  have h2 : b % 2 = 0 ∨ b % 2 = 1 := by 
    omega
  have h3 : c % 2 = 0 ∨ c % 2 = 1 := by 
    omega
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> ( 
    simp [Int.even_iff, Int.add_emod, h1, h2, h3]
    <;> omega
  )