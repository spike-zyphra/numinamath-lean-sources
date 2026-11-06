import Mathlib

theorem algebra_255229 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b = 3 * (b + c)) (h2 : b + c = 3 * (a + b)) :
    a / b = 3 ∧ b / c = 4 ∧ a / c = 13 := by
  have h3 : a = 2 * b + 3 * c := by
    linarith

  have h4 : c = 3 * a + 2 * b := by
    linarith

  rw [h3] at h4

  have h5 : c = -b := by 
    nlinarith

  have h6 : b < 0 := by
    nlinarith [hc, h5]

  linarith [hb, h6]