import Mathlib

theorem algebra_229684 (a b c d : ℝ) (h₀ : a + b + c + d = 1050000)
    (h₁ : d = a + c) (h₂ : a = b * (1 - 25 / 100)) (h₃ : a = c * (1 + 20 / 100)) :
    a = 210000 ∧ b = 280000 ∧ c = 175000 ∧ d = 385000 := by

  have h4 : b = 4 * a / 3 := by
    nlinarith

  have h5 : c = 5 * a / 6 := by
    nlinarith

  have h6 : d = 11 * a / 6 := by
    rw [h₁]
    rw [h5]
    linarith

  have h7 : a = 210000 := by
    have h8 : a + b + c + d = 1050000 := h₀
    rw [h4, h5, h6] at h8
    linarith

  have h8 : b = 280000 := by
    rw [show a = 210000 by linarith [h7]] at h4
    linarith

  have h9 : c = 175000 := by
    rw [show a = 210000 by linarith [h7]] at h5
    linarith

  have h10 : d = 385000 := by
    rw [show a = 210000 by linarith [h7]] at h6
    linarith

  exact ⟨by linarith [h7], by linarith [h8], by linarith [h9], by linarith [h10]⟩