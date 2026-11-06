import Mathlib

theorem algebra_283874 (h : ℝ → ℝ) (h₀ : h 0 = 4) (h₁ : ∀ n, h (n + 1) = h n * (1 + 50 / 100)) :
    h 0 + h 1 + h 2 + h 3 = 32.50 := by 
  have h1 : h 1 = 6 := by
    have eq1 := h₁ 0
    rw [h₀] at eq1
    norm_num at eq1 ⊢
    linarith

  have h2 : h 2 = 9 := by
    have eq1 := h₁ 1
    rw [h1] at eq1 
    norm_num at eq1 ⊢
    linarith

  have h3 : h 3 = 13.5 := by
    have eq1 := h₁ 2
    rw [h2] at eq1 
    norm_num at eq1 ⊢
    linarith

  rw [h₀, h1, h2, h3]
  norm_num