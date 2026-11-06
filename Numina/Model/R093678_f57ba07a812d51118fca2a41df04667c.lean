import Mathlib

theorem algebra_85691 {a b c d : ℝ} (h₀ : a = 2 * b + c) (h₁ : b = 2 * c + d)
    (h₂ : 2 * c = d + a - 1) (h₃ : d = a - c) :
    b = 2 / 9 := by
  have h4 : d = 2 * b := by
    rw [show a = 2 * b + c by linarith [h₀]] at h₃
    linarith
  have h5 : c = 4 * b - 1 := by
    rw [show d = 2 * b by linarith [h4]] at h₂
    rw [show a = 2 * b + c by linarith [h₀]] at h₂
    linarith
  rw [show c = 4 * b - 1 by linarith [h5], show d = 2 * b by linarith [h4]] at h₁
  linarith