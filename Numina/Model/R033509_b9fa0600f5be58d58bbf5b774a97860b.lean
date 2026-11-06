import Mathlib

theorem algebra_236523 (a b c d : ℝ) (h₁ : a + b + c + d = -2) (h₂ : a * b + a * c + a * d + b * c + b * d + c * d = 0) :
    a ≤ -1 ∨ b ≤ -1 ∨ c ≤ -1 ∨ d ≤ -1 := by

  by_contra h
  push_neg at h

  nlinarith [sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1), sq_nonneg (d + 1),
          h.1, h.2.1, h.2.2.1, h.2.2.2]