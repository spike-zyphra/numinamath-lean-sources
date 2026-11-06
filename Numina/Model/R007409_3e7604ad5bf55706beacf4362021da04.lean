import Mathlib

theorem algebra_13477 {f : ℝ → ℝ} (hf : ∃ p q : Polynomial ℝ, f = fun x => p.eval x / q.eval x)
    (h : ∀ x ≠ 0, 3 * f (1 / x) + 2 * f x / x = x ^ 2) : f (-2) = 67 / 20 := by 
  have eq1 := h (-2) (show (-2 : ℝ) ≠ 0 by norm_num)
  have eq2 := h (-1/2) (show (-1/2 : ℝ) ≠ 0 by norm_num)
  norm_num at eq1 eq2
  linarith