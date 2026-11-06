import Mathlib

theorem algebra_199849 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : b^2 - a^2 = c^2 - b^2) :
    1 / (a + c) - 1 / (b + c) = 1 / (a + b) - 1 / (a + c) := by
  have h1 : 0 < a + c := by
    linarith
  have h2 : 0 < a + b := by
    linarith
  have h3 : 0 < b + c := by
    linarith
  field_simp [(show 0 < a + c by linarith), (show 0 < b + c by linarith), 
      (show 0 < a + b by linarith)]
  nlinarith [h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]