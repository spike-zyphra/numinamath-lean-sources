import Mathlib

theorem algebra_104751 {a b c : ℝ}
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a = b)
    (h₂ : b = c)
    (h₃ : b = a + 2)
    (h₄ : c = b - 4)
    (h₅ : a * b = c * d + 40)
    (h₆ : b * c = a * d + 22) :
    a * b = 88 := by
  rw [show a = b by linarith [h₁]] at h₃
  linarith