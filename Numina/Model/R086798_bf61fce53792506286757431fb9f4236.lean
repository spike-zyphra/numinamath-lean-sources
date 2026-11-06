import Mathlib

theorem algebra_16964 (a : ℕ → ℝ) (h : ∀ n, ∑ i in Finset.range n, a i = n * n) :
    a 2007 = 4015 := by
  have eq1 := h 2008
  have eq2 := h 2007
  rw [Finset.sum_range_succ] at eq1
  norm_num at eq1 eq2
  linarith