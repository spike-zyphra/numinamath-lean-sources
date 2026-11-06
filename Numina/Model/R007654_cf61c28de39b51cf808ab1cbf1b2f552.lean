import Mathlib

theorem algebra_127422 (f : ℝ → ℝ) (h : ∀ x y, f (x - f y) = 1 - x - y) :
    ∀ y, f y = 1 / 2 - y := by 
  -- Substituting x = f(y) into the original equation to find a relation for f(y)
  have h1 : ∀ y, f 0 = 1 - f y - y := by
    intro y
    specialize h (f y) y 
    simp at h 
    linarith 
  -- Rearranging to express f(y) in terms of f(0)
  have eq1 : ∀ y, f y = 1 - y - f 0 := by 
    intro y 
    have h1' : f 0 = 1 - f y - y := h1 y 
    linarith 
  -- Now we need to determine f(0)
  have f0 : f 0 = 1 / 2 := by 
    have eq1' := eq1 0 
    simp at eq1' 
    linarith 
  -- Now we can substitute f(0) = 1/2 into eq1 to find f(y)
  intro y 
  specialize eq1 y 
  rw [f0] at eq1 
  linarith