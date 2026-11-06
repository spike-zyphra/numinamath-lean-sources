import Mathlib

theorem algebra_176629 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b = 40.5 * 60) (h2 : b + c = 37.5 * 60) (h3 : b = (a + c) / 2) :
    a + b + c = 58.5 * 60 := by
  ring_nf at h1 h2 h3 ⊢
  linarith [h1, h2, h3]