import Mathlib

theorem algebra_111726 (x y : ℕ) (h₀ : x + y = 100) (h₁ : 2*x+4*y=260) :
    x=70 ∧ y=30 := by 
  have h2 : y = 30 := by 
    omega
  have h3 : x = 70 := by 
    omega
  exact ⟨h3, h2⟩