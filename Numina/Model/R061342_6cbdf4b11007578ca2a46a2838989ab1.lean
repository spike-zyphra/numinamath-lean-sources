import Mathlib

theorem algebra_193291 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a = (2 / 5) * (a + b + c)) (h₂ : b / c = (3 / 2) / (4 / 3))
    (h₃ : c = a - 16) :
    a + b + c = 136 := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 8 * b = 9 * c := by
    have hc' : c ≠ 0 := by linarith
    field_simp at h₂ ⊢
    linarith
  have h5 : b = (9 / 8) * c := by
    linarith
  have h6 : a = c + 16 := by linarith
  rw [h6, h5] at h₁
  have h7 : c = 192 / 5 := by
    linarith
  have ha' : a = 272 / 5 := by
    rw [h7] at h6
    linarith
  have hb' : b = 216 / 5 := by
    rw [h7] at h5
    linarith
  linarith [ha', hb', h7]