import Mathlib

theorem inequalities_8760 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) ≥ 1 := by 
  have h4 : 0 < b + 2 * c := by nlinarith
  have h5 : 0 < c + 2 * a := by nlinarith
  have h6 : 0 < a + 2 * b := by nlinarith
  have h : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) - 1 ≥ 0 := by 
    have h1 : a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b) - 1 =
        (a * (c + 2 * a) * (a + 2 * b) + b * (b + 2 * c) * (a + 2 * b) + c * (b + 2 * c) * (c + 2 * a) - (b + 2 * c) * (c + 2 * a) * (a + 2 * b)) / ((b + 2 * c) * (c + 2 * a) * (a + 2 * b)) := by
      field_simp
      ring
    rw [h1]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (a * b - c * a),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    positivity
  linarith
  all_goals try { linarith }
  all_goals try { positivity }
  all_goals try { nlinarith }