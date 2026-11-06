import Mathlib

theorem algebra_277740 (d : ℝ) (h₀ : d > 0) (h₁ : 20 / d = 4 * (d - 20) / (3 * d)) :
    d = 35 := by
  have h2 : d ≠ 0 := by linarith
  have h4 : 20 = 4 * (d - 20) / 3 := by 
    field_simp [h2] at h₁ ⊢
    nlinarith
  have h5 : 60 = 4 * (d - 20) := by
    linarith [h4]
  have h6 : d = 35 := by
    linarith [h5]
  exact h6