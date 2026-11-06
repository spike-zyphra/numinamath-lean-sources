import Mathlib

theorem algebra_292513 {f : ℝ → ℝ} (h : ∀ x y, f (x - f y) = 1 - x - y) :
    ∀ z, f z = 1 / 2 - z := by
  have eq1 : ∀ y, f 0 = 1 - f y - y := by
    intro y
    have := h (f y) y
    norm_num at this ⊢
    linarith
  
  have eq2 : ∀ y, f y = 1 - y - f 0 := by
    intro y
    have eq1' := eq1 y
    linarith
  
  have eq3 : f 0 = 1 / 2 := by
    have eq4 : f 0 = 1 - f 0 := by
      specialize eq2 0
      linarith
    linarith
  
  intro z
  have eq5 : f z = 1 - z - f 0 := eq2 z
  rw [eq5]
  rw [eq3]
  ring