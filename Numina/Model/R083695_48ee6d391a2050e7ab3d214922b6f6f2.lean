import Mathlib

theorem algebra_294578 {a b c : ℕ} (h₀ : a + b + c = 98)
    (h₁ : a / 2 + b = c) (h₂ : b / 2 + c = a) :
    max (max a b) c = 52 := by
  omega