import Mathlib

theorem algebra_9243 (a : ℕ → ℝ) (h : ∀ x, (1 + x) ^ 16 = ∑ i in Finset.Icc 0 16, a i * x ^ i) :
    ∑ i in Finset.Icc 1 8, i * a i = 262144 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 := h 5
  have eq7 := h 6
  have eq8 := h 7
  have eq9 := h 8
  have eq10 := h 9
  have eq11 := h 10
  have eq12 := h 11
  have eq13 := h 12
  have eq14 := h 13
  have eq15 := h 14
  have eq16 := h 15
  have eq17 := h 16
  norm_num [Finset.sum_Icc_succ_top] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 ⊢
  linarith