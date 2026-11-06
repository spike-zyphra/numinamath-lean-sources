import Mathlib

theorem algebra_11549 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 10) (h₅ : a / b = 1) :
    (1 / 2) * a * b = 25 := by
  have h6 : a = b := by
    have h7 : b > 0 := h₁
    field_simp at h₅
    linarith
  have h9 : b = a := by linarith [h6]
  rw [show b = a by linarith [h6] ] at h₃
  rw [h₄] at h₃
  have h8 : a ^ 2 = 50 := by
    nlinarith
  have h10 : (1 / 2) * a * b = (1 / 2) * (a ^ 2) := by
    rw [show b = a by linarith [h6]]
    ring
  rw [h10]
  rw [h8]
  norm_num