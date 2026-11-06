import Mathlib

theorem algebra_11539 (a b c : ℝ) (h₀ : a = 6) (h₁ : b = 8) (h₂ : c = 10)
    (h₃ : d * 4 = (1 / 2) * a * b) :
    2 * (d + 4) = 20 := by 
  rw [h₀, h₁] at h₃
  have h₄ : d = 6 := by
    linarith 
  rw [h₄]
  norm_num