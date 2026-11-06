import Mathlib

theorem calculus_57616 (p : ℝ → ℝ) (h₀ : p 3.55 = -1 / 3) (h₁ : p 9.6 = 1 / 2)
    (h₂ : ∃ a b, ∀ x, p x = a * x + b) :
    p 5.97 = 0 := by
  rcases h₂ with ⟨a, b, h₂⟩
  have eq1 : p 3.55 = a * 3.55 + b := h₂ 3.55
  rw [eq1] at h₀
  have eq2 : p 9.6 = a * 9.6 + b := h₂ 9.6
  rw [eq2] at h₁
  have eq3 : p 5.97 = a * 5.97 + b := h₂ 5.97
  rw [eq3]
  norm_num at h₀ h₁ ⊢
  linarith