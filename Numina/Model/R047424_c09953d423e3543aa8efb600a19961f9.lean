import Mathlib

theorem inequalities_57922 (a b c d e f g h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : e < 0) (hf : f < 0) (hg : g < 0) (hh : h < 0) :
    (a * e + b * c) ≤ 0 ∨ (e * f + c * g) ≤ 0 ∨
    (f * d + g * h) ≤ 0 ∨ (d * a + h * b) ≤ 0 := by
  by_contra h1
  push_neg at h1

  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
    mul_neg_of_pos_of_neg ha he, mul_neg_of_pos_of_neg ha hf, mul_neg_of_pos_of_neg ha hg, mul_neg_of_pos_of_neg ha hh,
    mul_neg_of_pos_of_neg hb he, mul_neg_of_pos_of_neg hb hf, mul_neg_of_pos_of_neg hb hg, mul_neg_of_pos_of_neg hb hh,
    mul_neg_of_pos_of_neg hc he, mul_neg_of_pos_of_neg hc hf, mul_neg_of_pos_of_neg hc hg, mul_neg_of_pos_of_neg hc hh,
    mul_neg_of_pos_of_neg hd he, mul_neg_of_pos_of_neg hd hf, mul_neg_of_pos_of_neg hd hg, mul_neg_of_pos_of_neg hd hh,
    mul_pos_of_neg_of_neg he hf, mul_pos_of_neg_of_neg he hg, mul_pos_of_neg_of_neg he hh,
    mul_pos_of_neg_of_neg hf hg, mul_pos_of_neg_of_neg hf hh, mul_pos_of_neg_of_neg hg hh
    ]