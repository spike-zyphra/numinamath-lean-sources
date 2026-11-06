import Mathlib

theorem inequalities_67439 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (a^2 + 1) / (b + c) + (b^2 + 1) / (c + a) + (c^2 + 1) / (a + b) := by
  have h₁ : 0 < b + c := by linarith
  have h₂ : 0 < c + a := by linarith
  have h₃ : 0 < a + b := by linarith
  have h4 : (a^2 + 1) / (b + c) + (b^2 + 1) / (c + a) + (c^2 + 1) / (a + b) - 3 ≥ 0 := by 
    have h5 : (a^2 + 1) / (b + c) + (b^2 + 1) / (c + a) + (c^2 + 1) / (a + b) - 3 =
        ((a^2 + 1) * (c + a) * (a + b) + (b^2 + 1) * (b + c) * (a + b) + (c^2 + 1) * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by 
      field_simp
      ring
    rw [h5]
    have h6 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h8 : ((a^2 + 1) * (c + a) * (a + b) + (b^2 + 1) * (b + c) * (a + b) + (c^2 + 1) * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) ≥ 0 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    apply div_nonneg 
    linarith
    positivity
  linarith
  <;> try linarith