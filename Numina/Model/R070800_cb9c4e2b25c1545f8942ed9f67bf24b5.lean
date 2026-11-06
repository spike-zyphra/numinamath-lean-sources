import Mathlib

theorem algebra_178078 (a b c : ℝ) (h₀ : a + b + c > 0) (h₁ : a = (2 / 5) * (a + b + c))
    (h₂ : b / c = (3 / 2) / (4 / 3)) (h₃ : c = a - 16) :
    a + b + c = 136 := by
  
  have h₂₂ : c ≠ 0 := by
    by_contra h
    rw [h] at h₂ h₃
    norm_num at h₂
    all_goals linarith
  
  have h₄ : b / c = 9 / 8 := by
    have : b / c = (3 / 2) / (4 / 3) := h₂
    rw [this]
    field_simp
    <;> norm_num
  
  have h₅ : b = (9 / 8) * c := by
    have : b / c = 9 / 8 := h₄
    field_simp [h₂₂] at this
    linarith
  
  have h₆ : a = c + 16 := by
    linarith [h₃]

  rw [show a = c + 16 by linarith [h₆], show b = (9 / 8) * c by linarith [h₅]] at h₁
  
  have hc : c = 192 / 5 := by
    linarith
  
  have ha : a = 272 / 5 := by
    linarith [h₆, hc]
  
  have hb : b = 216 / 5 := by
    rw [show c = 192 / 5 by linarith [hc]] at h₅
    linarith
  
  have htotal : a + b + c = 136 := by
    linarith [ha, hb, hc]

  linarith