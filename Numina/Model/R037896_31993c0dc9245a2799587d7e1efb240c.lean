import Mathlib

theorem algebra_102221 {f : ℝ → ℝ} (h : ∀ x y, f (x - f y) = 1 - x - y) :
    ∀ x, f x = 1 / 2 - x := by

  have h1 : ∀ y, f 0 = 1 - f y - y := by
    intro y 
    specialize h (f y) y 
    simp at h 
    exact h

  have h2 : ∀ y, f y = 1 - f 0 - y := by
    intro y 
    have h3 := h1 y 
    linarith

  have h4 : f 0 = 1 / 2 := by
    have h5 := h2 0 
    norm_num at h5 
    linarith

  intro x 
  specialize h2 x 
  rw [h4] at h2
  linarith