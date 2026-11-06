import Mathlib

theorem algebra_210103 (v s : ℝ) (h₀ : v > 0) (h₁ : s > 0)
    (h₂ : v * 12 + 5 * (12 / 2) = 75) (h₃ : s * 12 + 5 * (12 * 2) = 75) :
    v * 9 + 5 * (9 / 2) = 75 ∧ s * 9 + 5 * (9 * 2) = 75 := by
  -- Simplify h₃.
  -- Multiply s by 12 and add 120 = 75.
  -- Contradicts with h₁ (s > 0).
  nlinarith