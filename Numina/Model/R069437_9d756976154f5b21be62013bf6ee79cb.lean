import Mathlib

theorem inequalities_30624 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) :
    a + b + c - a * b * c < 2 := by
  have h4 : 1 - a > 0 := by linarith
  have h5 : 1 - b > 0 := by linarith
  have h6 : 1 - c > 0 := by linarith
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
             mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith),
             mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith),
             mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith)]