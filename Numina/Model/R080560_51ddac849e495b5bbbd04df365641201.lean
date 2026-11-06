import Mathlib

theorem algebra_217747 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : 1 / a + 1 / b + 1 / c = 1 / 90)
    (h₂ : 1 / a + 1 / b + 1 / d = 1 / 120)
    (h₃ : 1 / c + 1 / d = 1 / 180) :
    (1 - (36 * (1 / a + 1 / b))) / (1 / a + 1 / b + 1 / c + 1 / d) = 60 := by
  have h4 : 1 / a + 1 / b = 1 / 144 := by
    have h5 : 1 / c - 1 / d = 1 / 360 := by
      have h6 : 1 / a + 1 / b + 1 / c = 1 / 90 := h₁
      have h7 : 1 / a + 1 / b + 1 / d = 1 / 120 := h₂
      linarith
    have h6 : 1 / c = 1 / 240 := by
      linarith [h₃, h5]
    have h7 : 1 / d = 1 / 720 := by
      linarith [h₃, h6]
    linarith [h₁, h6]
  have h8 : 1 / a + 1 / b + 1 / c + 1 / d = 1 / 80 := by
    have h6 : 1 / c = 1 / 240 := by
      have h5 : 1 / c - 1 / d = 1 / 360 := by
        have h6 : 1 / a + 1 / b + 1 / c = 1 / 90 := h₁
        have h7 : 1 / a + 1 / b + 1 / d = 1 / 120 := h₂
        linarith
      linarith [h₃, h5]
    have h7 : 1 / d = 1 / 720 := by
      linarith [h₃, h6]
    have h9 : 1 / a + 1 / b = 1 / 144 := h4
    linarith [h9, h6, h7]
  have h9 : 1 - (36 * (1 / a + 1 / b)) = 3 / 4 := by
    have h10 : 1 / a + 1 / b = 1 / 144 := h4
    rw [h10]
    norm_num
  rw [h9, h8]
  norm_num