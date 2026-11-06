import Mathlib

theorem algebra_7994 {a : ℕ → ℝ} (h : ∀ x, (-1-5*x+5*x^2)^2010 * (1+7*x-7*x^2)^2009 = ∑' n, a n * x ^ n) :
    ∑' n, a n = 1 := by 
  have eq1 := h 1
  simp at eq1 ⊢
  norm_num at eq1 ⊢
  linarith