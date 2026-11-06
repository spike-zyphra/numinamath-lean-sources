import Mathlib

theorem algebra_302915 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a - 1 = b - 2) (h2 : a - 100 = b - 1.01) :
    a - 100 = 1 := by
  ring_nf at h1 h2 ⊢
  linarith