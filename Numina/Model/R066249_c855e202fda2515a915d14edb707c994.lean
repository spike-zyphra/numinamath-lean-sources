import Mathlib

theorem algebra_232 {j a f : ℕ} (h₀ : j + a = f + 24) (h₁ : j + f = a + 10) (h₂ : f + a = j + 20) :
    j + a + f = 54 := by 
  omega