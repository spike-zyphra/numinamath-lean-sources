import Mathlib

theorem inequalities_90753 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b + c + 3) / 4 ≥ 1 / (a + b) + 1 / (b + c) + 1 / (c + a) := by
  have h1 : 0 < a * b := by nlinarith
  have h2 : 0 < a * c := by nlinarith
  have h3 : 0 < b * c := by nlinarith
  have h4 : 0 < (a + b) * (b + c) * (c + a) := by positivity
  have h5 : (a + b) > 0 := by positivity
  have h6 : (b + c) > 0 := by positivity
  have h7 : (c + a) > 0 := by positivity
  have h8 : (a + b + c + 3) / 4 - (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≥ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have h9 : (a + b + c + 3) / 4 - (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) =
        ((a + b + c + 3) * (a + b) * (b + c) * (c + a) - 4 * ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c))) / (4 * (a + b) * (b + c) * (c + a)) := by
      field_simp
      ring
    rw [h9] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * c - b * c), sq_nonneg (a * b - a * c), sq_nonneg (b * c - a * b),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          habc
        ]
    all_goals positivity
  linarith