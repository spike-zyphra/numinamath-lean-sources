import Mathlib

theorem algebra_260303 (a b c : ℕ) (h₀ : a + b + c = 100) (h₁ : a = 2 * b) (h₂ : c = a + 10) :
    c = 46 := by
  rw [h₁] at h₂ 
  rw [h₁, h₂] at h₀ 
  omega -- This tactic is powerful enough to solve the arithmetic goal