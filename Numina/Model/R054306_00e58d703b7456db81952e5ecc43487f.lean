import Mathlib

theorem algebra_281662 {a b c : ℕ} (h₀ : a = b + c + 16) (h₁ : a^2 = (b + c)^2 + 1632) :
    a + b + c = 102 := by
  rw [h₀] at h₁
  have h2 : (b + c + 16) ^ 2 = (b + c) ^ 2 + 1632 := h₁
  have h3 : 32 * (b + c) = 1376 := by
    nlinarith [h2]
  have h4 : b + c = 43 := by 
    omega
  have h5 : a = 59 := by
    omega
  omega