import Mathlib

theorem algebra_95436 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 1 / (a + b) = 2)
    (h₂ : 1 / (b + c) = 4)
    (h₃ : 1 / (a + c) = 2 + 2 / 5) :
    1 / a = 3 := by

  have h1 : a + b ≠ 0 := by
    have h4 : 0 < a := h₀.1
    have h5 : 0 < b := h₀.2.1
    linarith
  have h4 : a + b = 1 / 2 := by
    field_simp at h₁
    linarith

  have h5 : b + c ≠ 0 := by
    have h6 : 0 < b := h₀.2.1
    have h7 : 0 < c := h₀.2.2
    linarith
  have h6 : b + c = 1 / 4 := by
    field_simp at h₂
    linarith

  have h7 : a + c ≠ 0 := by
    have h8 : 0 < a := h₀.1
    have h9 : 0 < c := h₀.2.2
    linarith
  have h8 : a + c = 5 / 12 := by
    have eq1 : 1 / (a + c) = 12 / 5 := by
      norm_num at h₃ ⊢
      linarith
    field_simp [h7] at eq1
    linarith

  have h9 : a + b + c = 7 / 12 := by
    linarith [h4, h6, h8]

  have hc : c = 1 / 12 := by
    have h10 : c = (a + b + c) - (a + b) := by ring
    rw [h10, h9, h4]
    linarith

  have hb : b = 1 / 6 := by
    linarith [h6, hc]

  have ha : a = 1 / 3 := by
    linarith [h4, hb]

  have ha_pos : a ≠ 0 := by
    linarith [h₀.1]

  field_simp [ha_pos]
  linarith [ha]