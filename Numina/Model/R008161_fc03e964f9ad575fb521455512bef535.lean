import Mathlib

theorem algebra_178093 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a / b = (2 + 3 / 4) / (1 + 5 / 6))
    (h₄ : b / c = (1 + 5 / 6) / (1 + 3 / 8))
    (h₅ : a * 18 = b * 18 + 72) :
    a + b + c = 26 := by

  have h6 : a = 3 / 2 * b := by
    have h7 : b ≠ 0 := by linarith
    field_simp at h₃
    linarith

  have h8 : c = 3 / 4 * b := by
    have h9 : c ≠ 0 := by linarith
    field_simp at h₄
    linarith

  rw [show a = 3 / 2 * b by linarith [h6]] at h₅

  have hb : b = 8 := by
    linarith

  have ha : a = 12 := by
    rw [hb] at h6
    linarith

  have hc : c = 6 := by
    rw [hb] at h8
    linarith

  linarith [ha, hb, hc]