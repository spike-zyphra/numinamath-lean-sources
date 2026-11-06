import Mathlib

theorem algebra_2 (a : ℕ → ℤ) (h : ∀ n, ∑ i in Finset.range n, a i = n ^ 3 + 4 * n) :
    a 9 = 275 := by 
  have eq1 := h 10
  have eq2 := h 9
  rw [Finset.sum_range_succ] at eq1
  norm_num at eq1 eq2 
  linarith