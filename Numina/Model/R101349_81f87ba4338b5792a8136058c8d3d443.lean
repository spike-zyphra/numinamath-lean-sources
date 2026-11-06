import Mathlib

theorem inequalities_597461 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) ≥ a + b + c := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h2 : a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) - (a + b + c) ≥ 0 := by 
    have pos1 : 0 < a * b * c := h1 
    have h3 : a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) - (a + b + c) =
          (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) / (a * b * c) := by 
      field_simp [show 0 < b * c by positivity, show 0 < c * a by positivity, show 0 < a * b by positivity]
      ring 

    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

    all_goals positivity 

  linarith