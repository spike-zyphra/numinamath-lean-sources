import Mathlib

theorem algebra_16612 (total_people : ℕ) (h₀ : total_people = 100)
    (kinda_pink : ℕ) (purply : ℕ) (h₁ : kinda_pink = 60) (both : ℕ)
    (h₂ : both = 27) (neither : ℕ) (h₃ : neither = 17)
    (h : kinda_pink + purply - both + neither = total_people) : purply = 50 := by 
  subst h₀ h₁ h₂ h₃
  omega