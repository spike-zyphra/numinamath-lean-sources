import Mathlib

theorem algebra_288107 {a b c p q y : ℝ} (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a)
    (h₃ : p ≠ 7) (h₄ : 7 ≠ q) (h₅ : q ≠ 13) (h₆ : 2 ≠ 5) (h₇ : 5 ≠ 10) (h₈ : 10 ≠ 13)
    (h₉ : 13 ≠ 15) (h₁₀ : a + 21 = b + c) (h₁₁ : b + c = p + 7) (h₁₂ : p + 7 = q + 13)
    (h₁₃ : 2 * y + 3 = (y ^ 2 + 2) - (y - 6)) :
    a - b = 3 ∧ b - c = 3 ∧ p = 5 ∧ q = 1 := by
  have h₁₄ : y ^ 2 - 3 * y + 5 = 0 := by
    nlinarith
  have h₁₆ : (y - 3 / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  nlinarith [h₁₄, h₁₆]