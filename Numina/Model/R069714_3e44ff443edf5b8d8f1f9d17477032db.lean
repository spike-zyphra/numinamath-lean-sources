import Mathlib

theorem algebra_123502 (db f m : ℕ) (h₀ : db + f + m = 100)
    (h₁ : m - 6 = 4 * (db - 6)) (h₂ : f - 13 = 15 * (db - 13)) :
    db = 15 := by
  omega