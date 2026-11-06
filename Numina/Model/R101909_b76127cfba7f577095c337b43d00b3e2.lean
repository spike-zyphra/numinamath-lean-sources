import Mathlib

theorem algebra_305595 {f : ℝ → ℝ} (h0 : f 0 = 1) (h : ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) :
    ∀ x, f x = x + 1 := by 
  have h1 : f 1 = 2 := by 
    specialize h 0 0 
    simp at h 
    rw [h0] at h 
    linarith 
  intro x 
  have eq1 := h x 0 
  simp at eq1 
  rw [h0] at eq1 
  rw [h1] at eq1 
  linarith