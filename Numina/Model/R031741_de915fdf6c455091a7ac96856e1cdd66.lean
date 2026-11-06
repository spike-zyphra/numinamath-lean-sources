import Mathlib

theorem inequalities_162004 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a)) ≥ (a + b + c) / 2 := by
  have h1 : 0 < a + b := by nlinarith
  have h2 : 0 < b + c := by nlinarith
  have h3 : 0 < c + a := by nlinarith
  have h4 : a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) - (a + b + c) / 2 ≥ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have h5 : a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) - (a + b + c) / 2 =
        (a ^ 2 * (b + c) * (c + a) + b ^ 2 * (a + b) * (c + a) + c ^ 2 * (a + b) * (b + c) - (a + b + c) / 2 * (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
              sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    all_goals positivity
  linarith