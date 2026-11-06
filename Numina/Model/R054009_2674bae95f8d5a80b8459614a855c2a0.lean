import Mathlib

theorem algebra_128 {a b c : ℕ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0) (h₃ : a < b) (h₄ : a + b = c * 2) (h₅ : 50 * (a + b) = 25 * (a + b) + 48) (h₆ : 50 * (a + b) + 25 * (a + b) = 48): c = 80 := by
  omega