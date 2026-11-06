import Mathlib

theorem algebra_154325 {f : ℝ → ℝ} (hf : ∃ p q : Polynomial ℝ, f = fun x => p.eval x / q.eval x)
    (h : ∀ x, x ≠ 0 → 3 * f (1 / x) + 2 * f x / x = x ^ 2) : f (-2) = 67 / 20 := by 
  have eq1 := h (-2) (by norm_num)
  have eq2 := h (-1/2) (by norm_num)
  norm_num at eq1 eq2
  linarith [eq1, eq2]