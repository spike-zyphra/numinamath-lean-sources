import Mathlib

theorem algebra_93687 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = x + f y) (h' : f 0 = 2) :
    f 1998 = 2000 := by
  have h1 : ∀ x, f x = x + 2 := by
    intro x
    have eq1 := h x 0
    simp at eq1
    rw [h'] at eq1
    linarith
  have eq2 := h1 1998
  norm_num at eq2
  linarith