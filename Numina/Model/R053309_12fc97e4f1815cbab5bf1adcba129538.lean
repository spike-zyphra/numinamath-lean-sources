import Mathlib

theorem algebra_308082 (s : ℕ → ℝ) (h₀ : s 0 = 200) (h₁ : s 1 = 200 + 20)
    (h₂ : ∀ n, s (n + 1) = s n * (1 - 4 / 5)) :
    s 11 = 75 := by 
  have h3 := h₂ 0
  norm_num at h3 
  rw [h₀] at h3 
  norm_num at h3 
  linarith [h₁, h3]