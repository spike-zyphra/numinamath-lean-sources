import Mathlib

theorem algebra_204392 {a b : ℝ} (h₀ : a + b = 2) (h₁ : a^2 + b^2 = 6) :
    1 / a + 1 / b = -2 := by
  have h2 : a ≠ 0 := by 
    by_contra ha
    have ha' : a = 0 := by
      linarith 
    have hb : b = 2 := by 
      rw [ha'] at h₀ 
      linarith 
    rw [ha', hb] at h₁ 
    nlinarith 
  have h3 : b ≠ 0 := by 
    by_contra hb
    have hb' : b = 0 := by 
      linarith 
    have ha : a = 2 := by 
      rw [hb'] at h₀ 
      linarith 
    rw [ha, hb'] at h₁ 
    nlinarith 
  have h4 : a * b = -1 := by 
    have h2 : (a + b) ^ 2 = 4 := by 
      rw [h₀]
      norm_num 
    have h5 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by 
      ring 
    rw [h5] at h2 
    rw [h₁] at h2 
    linarith 
  have h5 : 1 / a + 1 / b = (a + b) / (a * b) := by 
    field_simp [h2, h3]
    <;> ring 
  rw [h5]
  rw [h₀, h4]
  norm_num