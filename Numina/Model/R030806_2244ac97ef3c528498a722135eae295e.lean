import Mathlib
theorem algebra_21234 {a b c d : ℝ}
    (h₀ : a + b + c + d = 1)
    (h₁ : a + 2 * b + 4 * c + 8 * d = 16)
    (h₂ : a - 5 * b + 25 * c - 125 * d = 625)
    (h₃ : a + 6 * b + 36 * c + 216 * d = 1296) :
    a = 60 ∧ b = -88 ∧ c = 25 ∧ d = 4 := by
  constructor
  · -- Prove a = 60
    linarith
  constructor
  · -- Prove b = -88
    linarith
  constructor
  · -- Prove c = 25
    linarith
  · -- Prove d = 4
    linarith