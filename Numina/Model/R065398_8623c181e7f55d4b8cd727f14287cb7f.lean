import Mathlib

open Real

theorem algebra_113653 {f : ℝ → ℝ → ℝ}
    (h₀ : ∀ x y, x > y → f x y = x)
    (h₁ : ∀ x y, x = y → f x y = 1)
    (h₂ : ∀ x y, x < y → f x y = y) :
    (f 1.1 (7 / 3) - f (1 / 3) 0.1) / f (4 / 5) 0.8 = 2 := by
  have h3 : f 1.1 (7 / 3 : ℝ) = 7 / 3 := by
    specialize h₂ 1.1 (7 / 3 : ℝ) (by norm_num)
    simpa using h₂
  
  have h4 : f (1 / 3 : ℝ) (0.1 : ℝ) = (1 / 3 : ℝ) := by 
    specialize h₀ (1 / 3 : ℝ) (0.1 : ℝ) (by norm_num)
    simpa using h₀
  
  have h5 : f (4 / 5 : ℝ) (0.8 : ℝ) = 1 := by 
    specialize h₁ (4 / 5 : ℝ) (0.8 : ℝ) (by norm_num)
    simpa using h₁
  
  rw [h3, h4, h5]
  norm_num