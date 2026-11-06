import Mathlib

theorem algebra_599898 (a : ℕ → ℝ) (h : ∀ x, ∑ i ∈ Finset.range 18, (-x) ^ i = ∑ i ∈ Finset.range 18, a i * (x + 1) ^ i) :
    a 2 = 816 := by
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
  simp [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18
  norm_num at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 eq12 eq13 eq14 eq15 eq16 eq17 eq18 
  have h1 : a 2 = 816 := by 
    linarith
  exact h1