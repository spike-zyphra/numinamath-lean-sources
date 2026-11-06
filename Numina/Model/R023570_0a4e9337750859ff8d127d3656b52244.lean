import Mathlib

theorem algebra_306500 (a : ℕ → ℝ) (h : ∀ x, (1 + x + x ^ 2 + x ^ 3) ^ 5 * (1 - x + x ^ 2 - x ^ 3) ^ 5 = ∑ i in Finset.range 31, a i * x ^ i) :
    a 15 = 0 := by 
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
  have eq18 := h 17
  have eq19 := h 18
  have eq20 := h 19
  have eq21 := h 20
  have eq22 := h 21
  have eq23 := h 22
  have eq24 := h 23
  have eq25 := h 24
  have eq26 := h 25
  have eq27 := h 26
  have eq28 := h 27
  have eq29 := h 28
  have eq30 := h 29
  have eq31 := h 30
  norm_num [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18 eq19 eq20 eq21 eq22 eq23 eq24 eq25 eq26 eq27 eq28 eq29 eq30 eq31 
  linarith