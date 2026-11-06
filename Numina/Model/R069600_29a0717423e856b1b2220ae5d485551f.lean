import Mathlib

theorem algebra_193648 (n m : ℕ) (h₀ : n * 50 + m * 60 = 1200) (h₁ : n = m + 5)
    (h₂ : n * (1200 ^ 2 - 50) = m * (1200 ^ 2 - 60)) :
    n + m = 45 := by
  norm_num at h₀ h₁ h₂ ⊢
  omega