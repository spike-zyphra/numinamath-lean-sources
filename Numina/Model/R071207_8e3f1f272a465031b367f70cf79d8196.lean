import Mathlib

theorem algebra_167989 (f : ℝ → ℝ) (h : ∀ x, 2 * f x + f (1 - x) = x ^ 2) :
    f = fun x => (1 / 3) * (x ^ 2 + 2 * x - 1) := by 
  funext x
  have eq1 := h x
  have eq2 := h (1 - x)
  rw [show 1 - (1 - x : ℝ) = x by ring] at eq2
  linarith