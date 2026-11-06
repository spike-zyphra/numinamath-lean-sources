import Mathlib

theorem algebra_12967 {a b c : ℤ} (h₀ : a + b + c = 19) (h₁ : a^2 + b^2 + c^2 = 2019) :
    a * b + b * c + c * a = -829 := by
  have h2 : (a + b + c) ^ 2 = 361 := by
    rw [h₀]
    norm_num
  have h3 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
    ring
  rw [h3] at h2
  rw [h₁] at h2
  linarith