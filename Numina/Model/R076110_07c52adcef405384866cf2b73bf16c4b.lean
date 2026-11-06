import Mathlib

theorem algebra_109089 (f : ℝ → ℝ) (h : ∀ x y, f (x + f y) = x + y) :
    f 2021 = 2021 := by
  have h1 : ∀ y, f (f y) = y := by 
    intro y
    have h2 := h 0 y
    simp at h2
    exact h2
  
  have h0 : f 0 = 0 := by 
    have h3 := h (-f 0) 0
    simp at h3
    linarith [h3]

  have h4 := h (2021 - f 0) 0 
  rw [show f 0 = 0 by linarith [h0]] at h4 
  norm_num at h4 ⊢ 
  linarith