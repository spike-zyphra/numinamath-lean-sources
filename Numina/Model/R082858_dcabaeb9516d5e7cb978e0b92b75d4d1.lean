import Mathlib

theorem algebra_156056 (d u : ℝ) (h₀ : d > 0) (h₁ : u > 0)
    (h₂ : d + u = 21) (h₃ : d / 4 + u / 6 = 4.25) :
    u / 4 + d / 6 = 4.5 := by
  have h4 : u = 21 - d := by linarith
  rw [h4] at h₃
  have h5 : d = 9 := by
    norm_num at h₃ ⊢
    linarith
  have h6 : u = 12 := by 
    rw [h5] at h4
    linarith
  rw [h5, h6]
  norm_num