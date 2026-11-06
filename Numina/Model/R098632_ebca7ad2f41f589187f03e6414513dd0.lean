import Mathlib

theorem algebra_156386 {f : ℝ → ℝ} (h : ∀ x y, f (x - f y) = 1 - x - y) :
    ∀ x, f x = 1 / 2 - x := by
  -- First, let's substitute x = f(y) into h to get an equation involving f(0)
  have h1 : ∀ y, f y = 1 - f 0 - y := by 
    intro y
    have h2 := h (f y) y
    simp at h2
    linarith
  have h3 := h (f 0) 0 
  norm_num at h3 
  -- Solve the equation f(0) = 1 - f(0) 
  have h2' : f 0 = 1 / 2 := by 
    linarith
  intro x 
  specialize h1 x 
  rw [h2'] at h1 
  linarith