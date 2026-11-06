import Mathlib

theorem calculus_6109 (f : ℝ → ℝ) (h : ∃ g, Differentiable ℝ g ∧ ∀ x, f x = g x)
    (h' : ∀ x y, f (x + y) = f x + x * y * (x + y - 1)) :
    ∃ c, ∀ x, f x = x ^ 3 / 3 - x ^ 2 / 2 + c * x := by 
  have eq1 : ∀ y, f y = f 0 := by 
    intro y 
    have eq2 := h' 0 y 
    simp at eq2 
    linarith 
  have eq3 := h' 1 1 
  have eq4 : f 2 = f 1 + 1 * 1 * (1 + 1 - 1) := by 
    specialize h' 1 1 
    norm_num at h' ⊢ 
    linarith 
  have eq5 : f 2 = f 0 := by 
    have eq6 : ∀ y, f y = f 0 := eq1 
    specialize eq6 2 
    linarith 
  have eq6 : f 1 = f 0 := by 
    have eq7 : ∀ y, f y = f 0 := eq1 
    specialize eq7 1 
    linarith 
  rw [eq5, eq6] at eq4 
  linarith