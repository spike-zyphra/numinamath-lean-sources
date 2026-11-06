import Mathlib

theorem algebra_111323 (a : Fin 13 → ℝ) (h : ∀ x, (x^2 + 2 * x - 2)^6 = ∑ i, a i * (x + 2)^i.1) : a 0 + ∑ i > 0, i * a i = 64 := by
  -- For all $x \in \mathbb{R}$, $(x^2 + 2 x - 2)^6 = \sum_{i=0}^{12} a_i \cdot (x+2)^i$
  have eq1 := h 0
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq1
  have eq2 := h 1
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq2
  have eq3 := h 2
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq3
  have eq4 := h 3
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq4
  have eq5 := h 4
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq5
  have eq6 := h 5
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq6
  have eq7 := h 6
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq7
  have eq8 := h 7
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq8
  have eq9 := h 8
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq9
  have eq10 := h 9
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq10
  have eq11 := h 10
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq11
  have eq12 := h 11
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq12
  have eq13 := h 12
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq13
  have eq14 := h 13
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq14

  -- We need $\sum_{i=0}^{12} i \cdot a_i = 64$.
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_filter]
  <;> norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
  <;> linarith