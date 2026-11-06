import Mathlib

theorem inequalities_276801 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    ¬(a + b < c + d ∧ (a + b) * (c + d) < a * b + c * d ∧ (a + b) * c * d < a * b * (c + d)) := by
  rintro ⟨h1, h2, h3⟩
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith),
    mul_pos (show 0 < a * c by nlinarith) (show 0 < b * d by nlinarith), mul_pos (show 0 < a * d by nlinarith) (show 0 < b * c by nlinarith)]