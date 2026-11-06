import Mathlib

theorem algebra_5858 (f : ℝ → ℝ) (hf : f = fun x => 6*x^3 + 23*x^2 + 16*x + 3) :
    f = fun x => (3*x + 1)*(2*x + 1)*(x + 3) := by
  funext x
  rw [hf]
  have eq1 : (6 * x ^ 3 + 23 * x ^ 2 + 16 * x + 3 : ℝ) = (3 * x + 1) * (2 * x + 1) * (x + 3) := by
    ring
  exact eq1