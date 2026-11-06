import Mathlib

theorem algebra_123304 (f : ℕ → ℕ) (h₀ : ∀ x, 8 ≤ x → 8 ≤ f x)
    (h₁ : ∀ x y, 4 ≤ x → 4 ≤ y → f (x + y) = f (x * y)) (h₂ : f 8 = 9) :
    f 9 = 9 := by

  have h3 : f 16 = 9 := by 
    have eq1 := h₁ 4 4 (by norm_num) (by norm_num)
    norm_num at eq1 
    have h4 : f 8 = 9 := h₂
    omega
  have h4 : f 64 = 9 := by
    have eq1 := h₁ 8 8 (by norm_num) (by norm_num)
    norm_num at eq1 
    have h5 : f 16 = 9 := h3
    omega
  have h5 : f 20 = 9 := by
    have eq2 := h₁ 4 16 (by norm_num) (by norm_num)
    norm_num at eq2 
    have h6 : f 64 = 9 := h4
    omega
  have eq1 := h₁ 4 5 (by norm_num) (by norm_num)
  norm_num at eq1 
  have h7 : f 20 = 9 := h5
  omega