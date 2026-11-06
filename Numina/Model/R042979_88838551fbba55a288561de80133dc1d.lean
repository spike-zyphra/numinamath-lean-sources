import Mathlib

theorem algebra_95182 (h w l k : ℝ) (h₀ : h = 2) (h₁ : w = 3) (h₂ : l = 5)
(h₃ : 40 = k * h * w * l) (n : ℝ) (hn : n = k * (2 * h) * (3 * w) * l) :
n = 240 := by
  rw [h₀] at h₃ hn
  rw [h₁] at h₃ hn
  rw [h₂] at h₃ hn
  norm_num at h₃ hn
  linarith