import Mathlib

theorem algebra_95690 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / 2 / v = 6) (h₃ : d / 2 / (3 * v) + 6 = t) :
    t = 8 := by 
  have h4 : d = 12 * v := by
    have h5 : d / 2 / v = 6 := h₂
    field_simp [h₁] at h5 ⊢
    linarith
  rw [h4] at h₃
  have h5 : (12 * v / 2 / (3 * v)) = 2 := by
    have h6 : v ≠ 0 := by linarith
    field_simp [h6]
    <;> ring_nf <;> nlinarith
  have h6 : t = 8 := by
    have h7 : (12 * v / 2 / (3 * v)) + 6 = t := by linarith
    rw [h5] at h7
    linarith
  linarith