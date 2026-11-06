import Mathlib

theorem algebra_278527 {a b c : ℝ} (h₀ : a + b + c = 15) (h₁ : a + b - c = 10)
    (h₂ : a - b + c = 8) :
    a = 9 ∧ b = 3.5 ∧ c = 2.5 := by 
  have h3 : a = 9 := by 
    linarith 
  have hb : b = 3.5 := by
    have eq1 := h₀
    rw [h3] at eq1 
    have eq2 := h₁ 
    rw [h3] at eq2 
    have h4 : b + c = 6 := by linarith 
    have h5 : b - c = 1 := by linarith 
    have h6 : 2 * b = 7 := by 
      linarith [h4, h5] 
    have hb' : b = 7 / 2 := by 
      linarith 
    rw [hb']
    norm_num 
  have hc : c = 2.5 := by 
    have eq1 := h₀ 
    rw [h3] at eq1 
    have h4 : b + c = 6 := by linarith 
    rw [hb] at h4 
    have hc' : c = 2.5 := by 
      linarith 
    exact hc' 
  exact ⟨h3, hb, hc⟩