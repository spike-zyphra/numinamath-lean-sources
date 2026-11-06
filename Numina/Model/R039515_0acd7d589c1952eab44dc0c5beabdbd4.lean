import Mathlib

theorem algebra_219887 (v s : ℝ) (h₀ : 0 < v) (h₁ : 0 < s)
    (h₂ : 80 / (v + s) + 48 / (v - s) = 9) (h₃ : 64 / (v + s) + 96 / (v - s) = 12) :
    v = 14 := by
  have h4 : v + s ≠ 0 := by
    nlinarith
  have h5 : v - s ≠ 0 := by
    by_contra h
    have : v = s := by linarith
    rw [show v - s = (0 : ℝ) by linarith] at h₂ h₃
    field_simp [show v + s ≠ 0 from by linarith] at h₂ h₃
    <;> nlinarith
  have h6 : 80 * (v - s) + 48 * (v + s) = 9 * (v + s) * (v - s) := by 
    have eq1' : 80 / (v + s) + 48 / (v - s) = 9 := h₂
    field_simp [h4, h5] at eq1' ⊢
    linarith
  have h7 : 64 * (v - s) + 96 * (v + s) = 12 * (v + s) * (v - s) := by 
    have eq2' : 64 / (v + s) + 96 / (v - s) = 12 := h₃ 
    field_simp [h4, h5] at eq2' ⊢ 
    linarith
  have h8 : (v - 14) ^ 2 = 0 := by
    nlinarith [sq_nonneg (v - 14), sq_nonneg (s - 2), mul_pos h₀ h₁]
  have h9 : v - 14 = 0 := by
    nlinarith
  linarith