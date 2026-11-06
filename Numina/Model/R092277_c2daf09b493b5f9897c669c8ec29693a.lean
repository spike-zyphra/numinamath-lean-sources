import Mathlib

theorem inequalities_116000 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by 
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h2 : 0 < (b + c) * (c + a) * (a + b) := by
      apply mul_pos
      apply mul_pos
      linarith [hb, hc]
      linarith [ha, hc]
      linarith [ha, hb]
 
    have h3 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
      ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - (3 / 2) * (b + c) * (c + a) * (a + b) ) ) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring

    rw [h3]

    have h4 : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - (3 / 2) * (b + c) * (c + a) * (a + b) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

    apply div_nonneg 
    linarith [h4]
    linarith [h2]

  linarith [h1]