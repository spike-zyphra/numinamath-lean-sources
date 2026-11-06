import Mathlib

theorem algebra_5775 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) + x = x * f y + f x) (h' : f (-1) = 5) :
    f (-1001) = 2005 := by 
  have eq3 : ∀ x, f x = f 0 + x - x * f 0 := by
    intro x
    have eq4 := h x 0
    simp at eq4
    linarith 
  have eq5 := eq3 (-1)
  rw [h'] at eq5
  have f0 : f 0 = 3 := by 
    linarith 
  have eq6 : ∀ x, f x = 3 - 2 * x := by 
    intro x 
    specialize eq3 x 
    rw [f0] at eq3 
    have eq6 : f x = 3 - 2 * x := by 
      linarith 
    exact eq6 
  have final : f (-1001) = 2005 := by
    specialize eq6 (-1001) 
    linarith 
  exact final