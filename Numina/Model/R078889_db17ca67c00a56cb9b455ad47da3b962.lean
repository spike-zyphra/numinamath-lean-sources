import Mathlib

theorem algebra_291649 {f : ℝ → ℝ → ℝ} (h1 : ∀ x, f x x = 0)
    (h2 : ∀ x y z, f x (f y z) = f x y + z) :
    f 2021 1999 = 22 := by 
  have h3 : ∀ x y, f x y = f x 0 - y := by
    intro x y 
    have h4 := h2 x y y 
    have h5 : f y y = 0 := h1 y 
    simp [h5] at h4 
    linarith 
  have h4 : ∀ x, f x 0 = x := by 
    intro x 
    have h5 : f x x = 0 := h1 x 
    have h6 : f x x = f x 0 - x := h3 x x 
    rw [h5] at h6 
    linarith 
  have h7 : ∀ x y, f x y = x - y := by 
    intro x y 
    have h8 : f x 0 = x := h4 x 
    have h9 : f x y = f x 0 - y := h3 x y 
    rw [h8] at h9 
    linarith 
  specialize h7 2021 1999 
  norm_num at h7 ⊢ 
  linarith