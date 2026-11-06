import Mathlib

theorem algebra_237400 (z g r : ℝ) (h₀ : z + g + r = 2000) (h₁ : z / g = 2 / 3) (h₂ : g / r = 9 / 5) :
    z = 600 ∧ g = 900 ∧ r = 500 := by
  have g_ne_zero : g ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have r_ne_zero : r ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
  have h3 : 3 * z = 2 * g := by
    field_simp [g_ne_zero] at h₁
    linarith
  have h4 : 5 * g = 9 * r := by
    field_simp [r_ne_zero] at h₂
    linarith
  have h5 : z = (2 / 3) * g := by
    linarith
  have h6 : r = (5 / 9) * g := by
    linarith
  rw [h5, h6] at h₀
  have h7 : g = 900 := by
    linarith
  have h8 : z = 600 := by
    rw [h7] at h5
    linarith
  have h9 : r = 500 := by
    rw [h7] at h6
    linarith
  exact ⟨h8, h7, h9⟩