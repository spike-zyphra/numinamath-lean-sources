import Mathlib

theorem inequalities_155643 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (b + a) ≥ 3 / 2 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < a + c := by linarith
  have h9 : 0 < b + a := by linarith

  have h5 : a / (b + c) + b / (a + c) + c / (b + a) - 3 / 2 ≥ 0 := by
    have h6 : (a / (b + c) + b / (a + c) + c / (b + a) - 3 / 2) =
      (2 * (a * (a + c) * (b + a) + b * (b + c) * (b + a) + c * (b + c) * (a + c)) - 3 * (b + c) * (a + c) * (b + a)) / (2 * (b + c) * (a + c) * (b + a)) := by
      field_simp
      ring
    rw [h6]
    have h7 : 0 < 2 * (b + c) * (a + c) * (b + a) := by positivity
    have h8 : 2 * (a * (a + c) * (b + a) + b * (b + c) * (b + a) + c * (b + c) * (a + c)) - 3 * (b + c) * (a + c) * (b + a) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    apply div_nonneg
    linarith
    positivity
  
  linarith