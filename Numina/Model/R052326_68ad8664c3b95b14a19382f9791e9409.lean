import Mathlib

theorem inequalities_149555 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) > 1 := by 
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < a + c := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 1 > 0 := by
    have denomin_pos : 0 < (b + c) * (a + c) * (a + b) := by positivity
    have numer_pos : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - (b + c) * (a + c) * (a + b) > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        sq_nonneg (a + b + c - b - c), sq_nonneg (a + b + c - a - b), sq_nonneg (a + b + c - a - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos ha (show 0 < a * b by nlinarith), mul_pos ha (show 0 < a * c by nlinarith), 
        mul_pos hb (show 0 < b * c by nlinarith)]
    have h5 : a / (b + c) + b / (a + c) + c / (a + b) - 1 =
        (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - (b + c) * (a + c) * (a + b)) / ((b + c) * (a + c) * (a + b)) := by
      field_simp [h1, h2, h3]
      ring
    rw [h5]
    apply div_pos
    · linarith
    · positivity
  linarith [h4]