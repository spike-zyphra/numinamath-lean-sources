import Mathlib

theorem inequalities_91381 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (2 * (a * b + b * c + c * a)) ≤ 1 / ((a + b) * b) + 1 / ((b + c) * c) + 1 / ((c + a) * a) := by
  have h1 : 0 < a * b := by positivity
  have h2 : 0 < b * c := by positivity
  have h3 : 0 < c * a := by positivity
  have h4 : 0 < a * b + b * c + c * a := by positivity

  have h5 : 0 < (a + b) * b := by positivity
  have h6 : 0 < (b + c) * c := by positivity
  have h7 : 0 < (c + a) * a := by positivity

  have h8 : 1 / ((a + b) * b) + 1 / ((b + c) * c) + 1 / ((c + a) * a) - 9 / (2 * (a * b + b * c + c * a)) ≥ 0 := by
    have h9 : (1 / ((a + b) * b) + 1 / ((b + c) * c) + 1 / ((c + a) * a) - 9 / (2 * (a * b + b * c + c * a)) ) =
        (2 * (a * b + b * c + c * a) * (b + c) * c * (c + a) * a + 2 * (a * b + b * c + c * a) * (a + b) * b * (c + a) * a + 2 * (a * b + b * c + c * a) * (a + b) * b * (b + c) * c - 9 * (a + b) * b * (b + c) * c * (c + a) * a) / ((a + b) * b * (b + c) * c * (c + a) * a * (2 * (a * b + b * c + c * a))) := by 
      field_simp
      ring
    rw [h9] at *
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
    ]
    all_goals positivity 
  linarith [h8]