import Mathlib

theorem inequalities_224667 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a / b < c / d) :
    a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d := by

  have h1 : a * d < b * c := by
    have h1 : a / b < c / d := h
    have h2 : 0 < b * d := mul_pos hb hd
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h1
    nlinarith [h1,  mul_pos ha hb, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]

  constructor
  · apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1, mul_pos ha hd, mul_pos ha hc, mul_pos ha hb, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos ha hc, mul_pos hc hd, mul_pos hd hd, mul_pos hb hd, mul_pos hc hb]
  · apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1, mul_pos ha hd, mul_pos ha hc, mul_pos ha hb, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos ha hc, mul_pos hc hd, mul_pos hd hd, mul_pos hb hd, mul_pos hc hb]