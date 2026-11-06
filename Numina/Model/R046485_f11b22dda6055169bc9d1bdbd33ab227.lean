import Mathlib

theorem algebra_2739 {a : ℤ} (ha : a ≠ 0) (h : ∀ n : ℕ, Odd n → a^n = -a) :
    False := by 
  have h1 := h 1 (by decide)
  have h2 : a = -a := by 
    simpa using h1
  have h3 : a = 0 := by 
    linarith
  contradiction