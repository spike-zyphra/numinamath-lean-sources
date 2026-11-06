import Mathlib

theorem algebra_314737 (a : ℕ → ℝ) (h : ∀ x, (x^2 - x - 2)^3 = ∑ i in Finset.range 7, a i * x^i) :
    a 1 + a 3 + a 5 = -4 := by
  have eq1 := h 1
  have eq2 := h (-1)
  have eq3 := h 0
  have eq4 := h 2
  have eq5 := h 3
  have eq6 := h 4
  have eq7 := h 5
  simp [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  linarith