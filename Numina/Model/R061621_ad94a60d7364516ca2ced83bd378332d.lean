import Mathlib

theorem algebra_228534 (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b + c + d = 288) (h₂ : a = b + 36) (h₃ : a = (3 / 4) * (b + c))
    (h₄ : d = 2 * c) :
    a = 72 ∧ b = 36 ∧ c = 60 ∧ d = 120 := by
  have h5 : b = 3 * c - 144 := by
    rw [h₂] at h₃
    linarith
  have h6 : 2 * b + 3 * c = 252 := by
    rw [show a = b + 36 by linarith [h₂], show d = 2 * c by linarith [h₄]] at h₁
    linarith
  have h7 : c = 60 := by
    rw [show b = 3 * c - 144 by linarith [h5]] at h6
    linarith
  have h8 : b = 36 := by
    rw [h7] at h5
    linarith
  have h9 : a = 72 := by
    rw [h8] at h₂
    linarith
  have h10 : d = 120 := by
    rw [h7] at h₄
    linarith
  exact ⟨h9, h8, h7, h10⟩