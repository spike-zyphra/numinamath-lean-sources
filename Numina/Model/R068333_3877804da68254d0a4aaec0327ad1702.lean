import Mathlib

theorem algebra_213399 {f : ℝ → ℝ} (h0 : f 0 = 1)
    (h : ∀ x y, f (x * y + 1) = f x * f y - f y - x + 2) :
    ∀ x, f x = x + 1 := by
  -- Prove that f(1) = 2
  have h1 : f 1 = 2 := by 
    have eq1 := h 0 0
    simp [h0] at eq1
    norm_num at eq1 
    linarith
  
  intro x 
  have eq2 := h x 0 
  simp [h0, h1] at eq2 
  have eq3 : f x = x + 1 := by 
    linarith
  exact eq3