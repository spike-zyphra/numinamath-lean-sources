import Mathlib

theorem algebra_241636 (h k d : ℝ) (h₀ : h > 0) (h₁ : k > 0) (h₂ : d > 0)
    (h₃ : h / 10 + k / 8 + d / 16 = 6) (h₄ : h / 10 + k / 16 + d / 8 = 5)
    (h₅ : h = 17.5) :
    h + k + d = 57.5 := by
  rw [h₅] at h₃ h₄
  norm_num at h₃ h₄
  have eq1 : k = 28 := by
    linarith [h₃, h₄]
  have eq2 : d = 12 := by
    linarith [h₄, eq1]
  rw [h₅, eq1, eq2]
  norm_num