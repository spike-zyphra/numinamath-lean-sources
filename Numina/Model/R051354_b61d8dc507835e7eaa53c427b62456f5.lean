import Mathlib

theorem algebra_256425 (a : ℕ → ℤ) (h₀ : ∀ n, a (n + 2) = a n + a (n + 1)) (h₁ : a 1 = 1)
    (h₂ : a 4 = 2005) : a 5 = 3008 := by
  have a2_eq : a 2 = a 0 + a 1 := by 
    specialize h₀ 0 
    simpa using h₀ 
  have a3_eq : a 3 = a 1 + a 2 := by 
    specialize h₀ 1 
    simpa using h₀ 
  have a4_eq : a 4 = a 2 + a 3 := by 
    specialize h₀ 2 
    simpa using h₀ 
  rw [a3_eq, a2_eq, h₁] at a4_eq 
  have a0_val : a 0 = 1001 := by 
    linarith [h₂, a4_eq]
  have a2_val : a 2 = 1002 := by 
    rw [h₁, a0_val] at a2_eq 
    linarith
  have a3_val : a 3 = 1003 := by 
    rw [h₁, a2_val] at a3_eq 
    linarith 
  have a5_eq : a 5 = a 3 + a 4 := by 
    specialize h₀ 3 
    simpa using h₀ 
  rw [a3_val, h₂] at a5_eq 
  linarith