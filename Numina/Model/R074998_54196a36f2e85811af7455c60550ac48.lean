import Mathlib

theorem algebra_12971 {s t : ℝ} (h₀ : s ≠ 0) (h₁ : t ≠ 0)
    (h₂ : 10 * s + 0 = 6 * t + 0) :
    s / t = 3 / 5 := by 
  have h3 : 10 * s = 6 * t := by linarith
  have h4 : s = (3 / 5) * t := by
    linarith
  have h5 : s / t = 3 / 5 := by
    field_simp [h₁]
    linarith
  exact h5