import Mathlib

theorem number_theory_12760 (n : ℕ) (h₀ : n % 3 = 2) : (5 * n) % 3 = 1 := by 
  have h : n % 3 = 2 := h₀
  omega