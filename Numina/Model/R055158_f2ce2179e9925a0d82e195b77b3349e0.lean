import Mathlib

theorem algebra_57152 (b j s : ℕ) (h₀ : b > 0) (h₁ : j > 0) (h₂ : s > 0)
    (h₃ : 2 * b + 3 * j + 4 * s = 74) (h₄ : 2 * j + 3 * s + 4 * b = 91) :
    b^2 + j^2 + s^2 = 314 := by
  have h5 : b = 15 := by
    omega
  have h6 : j = 8 := by
    rw [h5] at h₃ h₄
    omega
  have h7 : s = 5 := by
    rw [h6] at h₃
    rw [h5] at h₃
    omega
  rw [h5, h6, h7]
  all_goals norm_num