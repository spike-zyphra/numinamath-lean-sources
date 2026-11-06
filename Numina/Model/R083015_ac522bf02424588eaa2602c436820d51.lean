import Mathlib

theorem algebra_19119 {d e : ℝ} (h₁ : 2 * d = 17 * e - 8) (h₂ : 2 * e = d - 9) :
    e = 2 := by 
  have h3 : d = 2 * e + 9 := by 
    linarith
  rw [h3] at h₁
  linarith