import Mathlib

theorem algebra_238277 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a * 10 = b * 15) (h2 : b * 15 = a * 20 + b * 25) :
    1 / a + 1 / b = 60 := by
  have h3 : a = 3 / 2 * b := by 
    linarith
  rw [h3] at h2
  have h4 : b > 0 := hb
  have h5 : b * (-40) = 0 := by 
    nlinarith 
  have h6 : b = 0 := by 
    nlinarith
  linarith