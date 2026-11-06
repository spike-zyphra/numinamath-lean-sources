import Mathlib

theorem algebra_284227 (f : ℝ → ℝ → ℝ) (h : ∀ x y z, f x y = f x z - 2 * f y z - 2 * z) :
    f 2005 1000 = 5 := by 
  have h1 : ∀ x, f x x = -x := by
    intro x
    have h2 := h x x x
    simp at h2
    linarith
  
  have h2 := h 2005 1000 2005
  have h3 := h 1000 2005 1000
  
  norm_num [h1] at h2 h3
  linarith [h2, h3]