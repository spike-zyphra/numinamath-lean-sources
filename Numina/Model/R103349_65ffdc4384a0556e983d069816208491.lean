import Mathlib

theorem algebra_3388 {a b c d : ℝ} (h₀ : a / b = 7 / 3) (h₁ : c / d = 8 / 5) :
    a * d / (b * c) = 35 / 24 := by
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀ 
  have h3 : d ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁ 
  have ha : a = 7 / 3 * b := by
    have h4 : b ≠ 0 := h2
    field_simp [h4] at h₀ 
    linarith 
  have hc : c = 8 / 5 * d := by
    have h5 : d ≠ 0 := h3
    field_simp [h5] at h₁ 
    linarith
  have hcd : c ≠ 0 := by 
    intro h 
    have h5 : d ≠ 0 := h3 
    have hc' : c = 8 / 5 * d := hc 
    rw [hc'] at h 
    have h6 : 8 / 5 * d = 0 := by linarith 
    have h7 : d = 0 := by 
      linarith 
    contradiction 
  have had : a ≠ 0 := by 
    intro h 
    have h2' : b ≠ 0 := h2 
    have ha' : a = 7 / 3 * b := ha 
    rw [ha'] at h 
    have h8 : 7 / 3 * b = 0 := by linarith 
    have h9 : b = 0 := by 
      linarith 
    contradiction 
  have h5 : b * c ≠ 0 := by 
    apply mul_ne_zero 
    exact h2 
    exact hcd 
  have h6 : a * d / (b * c) = (7 / 3 * b * d) / (b * (8 / 5 * d)) := by 
    rw [ha, hc] 
  rw [h6]
  -- Now simplify the expression 
  field_simp [h5, h2, h3, had, hcd] 
  <;> ring_nf <;> linarith 
  all_goals 
    linarith 
  all_goals 
    norm_num 
  all_goals 
    linarith 
  all_goals 
    norm_num 
  all_goals 
    linarith