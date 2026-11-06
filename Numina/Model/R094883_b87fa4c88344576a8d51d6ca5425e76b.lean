import Mathlib

theorem algebra_11192 (n : ℕ) (h₀ : n < 10) (h₁ : 6 ∣ 52280 + n) :
    n = 4 := by 
  have h2 : n < 10 := h₀
  omega