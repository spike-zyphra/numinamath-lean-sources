import Mathlib

theorem algebra_99998 (a : ℕ → ℝ) (h : ∀ x, (1 + x - x ^ 2) ^ 10 = ∑ i in Finset.range 21, a i * x ^ i) :
    a 0 + ∑ i in Finset.range 20, (i + 1) * a (i + 1) = -9 := by 
  have eq1 := h 0 
  simp [Finset.sum_range_succ] at eq1 
  have eq2 := h 1 
  norm_num [Finset.sum_range_succ] at eq2 
  have eq3 := h 2 
  norm_num [Finset.sum_range_succ] at eq3 
  have eq4 := h 3 
  norm_num [Finset.sum_range_succ] at eq4 
  have eq5 := h 4 
  norm_num [Finset.sum_range_succ] at eq5 
  have eq6 := h 5 
  norm_num [Finset.sum_range_succ] at eq6 
  have eq7 := h 6 
  norm_num [Finset.sum_range_succ] at eq7 
  have eq8 := h 7 
  norm_num [Finset.sum_range_succ] at eq8 
  have eq9 := h 8 
  norm_num [Finset.sum_range_succ] at eq9 
  have eq10 := h 9 
  norm_num [Finset.sum_range_succ] at eq10 
  have eq11 := h 10 
  norm_num [Finset.sum_range_succ] at eq11 
  have eq12 := h 11 
  norm_num [Finset.sum_range_succ] at eq12 
  have eq13 := h 12 
  norm_num [Finset.sum_range_succ] at eq13 
  have eq14 := h 13 
  norm_num [Finset.sum_range_succ] at eq14 
  have eq15 := h 14 
  norm_num [Finset.sum_range_succ] at eq15 
  have eq16 := h 15 
  norm_num [Finset.sum_range_succ] at eq16 
  have eq17 := h 16 
  norm_num [Finset.sum_range_succ] at eq17 
  have eq18 := h 17 
  norm_num [Finset.sum_range_succ] at eq18 
  have eq19 := h 18 
  norm_num [Finset.sum_range_succ] at eq19 
  have eq20 := h 19 
  norm_num [Finset.sum_range_succ] at eq20 
  have eq21 := h 20 
  norm_num [Finset.sum_range_succ] at eq21 
  norm_num [Finset.sum_range_succ]
  linarith