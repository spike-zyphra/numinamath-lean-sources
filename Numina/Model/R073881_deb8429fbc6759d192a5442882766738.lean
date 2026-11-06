import Mathlib

theorem algebra_2549 {f g : Polynomial ℝ} (hf : f = 3 * X ^ 2 + 5 * X - 2)
    (hg : g + f = X ^ 2 - 2 * X + 4) :
    g = -2 * X ^ 2 - 7 * X + 6 := by 
  have h1 : g = (X ^ 2 - 2 * X + 4) - f := by 
    rw [← hg]
    ring
  rw [h1, hf]
  ring