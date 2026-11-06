import Mathlib

theorem algebra_20636 (j j_dad : ℕ) (h₀ : j_dad = j + 31) (h₁ : j + j_dad = 53) :
    j_dad = 42 := by
  rw [h₀] at h₁
  have h2 : j = 11 := by 
    omega
  have h3 : j_dad = 42 := by 
    omega
  exact h3