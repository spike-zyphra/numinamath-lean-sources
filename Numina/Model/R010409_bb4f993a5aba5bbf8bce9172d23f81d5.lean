import Mathlib

theorem algebra_12830 {a : ℕ → ℝ} (h : ∀ x, x^5 + 3*x^3 + 1 = ∑ i in Finset.range 6, a i * (x - 1)^i) : a 3 = 13 := by
  have eq1 := h 1
  have eq2 := h 2
  have eq3 := h 3
  have eq4 := h 4
  have eq5 := h 5
  have eq6 := h 6
  norm_num [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 ⊢
  linarith