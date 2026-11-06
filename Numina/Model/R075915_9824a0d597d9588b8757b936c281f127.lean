import Mathlib

theorem number_theory_297924 (a b c : ℤ) (h₀ : a = 2) (h₁ : b = 2) (h₂ : c = 2)
    (h₃ : a = b - 1 + c ∨ b = a - 1 + c ∨ c = a + b) :
    a = 3 ∧ b = 3 ∧ c = 3 := by
  rcases h₃ with h | h | h
  · -- Assume the first disjunction holds
    rw [h₀, h₁, h₂] at h
    omega -- This will detect the contradiction
  · -- Assume the second disjunction holds
    rw [h₀, h₁, h₂] at h
    omega -- This will detect the contradiction
  · -- Assume the third disjunction holds
    rw [h₀, h₁, h₂] at h
    omega -- This will detect the contradiction