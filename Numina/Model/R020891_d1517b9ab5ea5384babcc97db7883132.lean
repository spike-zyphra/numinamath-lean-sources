import Mathlib

theorem algebra_181698 (a b c d e f : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (h1 : a = b + c) (h2 : b = c + d)
    (h3 : c = d + e) (h4 : d = e + f) (h5 : e = f + a) (h6 : f = a * b) :
    a + b + c + d + e + f = 4.5 := by 
  have eq1 : a = b + c := h1
  have eq2 : b = c + d := h2
  have eq3 : c = d + e := h3
  have eq4 : d = e + f := h4
  have eq5 : e = f + a := h5
  have eq6 : f = a * b := h6
  nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero hd, sq_pos_of_ne_zero he, sq_pos_of_ne_zero hf, sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + d), sq_nonneg (d + e), sq_nonneg (e + f), sq_nonneg (f + a)]