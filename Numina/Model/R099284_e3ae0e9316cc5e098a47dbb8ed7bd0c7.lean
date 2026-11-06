import Mathlib

theorem algebra_265436 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) (h2 : 1 / b + 1 / a + 1 / c = 1 / (a + b + c) + 0.5)
    (h3 : 1 / c + 1 / b + 1 / a = 1 / (a + b + c) + 1) (h4 : 1 / b = 30) :
    1 / a + 1 / b + 1 / c = 7.5 := by 
  have h5 : 1 / a + 1 / b + 1 / c = 1 / b + 1 / a + 1 / c := by 
    ring
  have h6 : 1 / a + 1 / b + 1 / c = 1 / (a + b + c) := h1
  have h7 : 1 / b + 1 / a + 1 / c = 1 / (a + b + c) := by
    linarith [h5, h6]
  linarith [h2, h7]