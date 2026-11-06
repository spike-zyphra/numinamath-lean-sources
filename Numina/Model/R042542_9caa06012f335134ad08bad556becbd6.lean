import Mathlib

theorem inequalities_599139 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ ((2 * a - b - c) ^ 2) / (2 * (a + b + c) ^ 2) := by 
  have pos1 : 0 < (b + c) * (c + a) * (a + b) := by
    positivity
  have pos2 : 0 < (a + b + c) ^ 2 := by
    positivity
  have h12 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) - ((2 * a - b - c) ^ 2) / (2 * (a + b + c) ^ 2) ≥ 0 := by
    have pos3 : 0 < (b + c) * (c + a) * (a + b) * (a + b + c) ^ 2 := by
      positivity
    have h13 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) - ((2 * a - b - c) ^ 2) / (2 * (a + b + c) ^ 2) =
        (2 * a * (a + b + c) ^ 2 * (c + a) * (a + b) + 2 * b * (a + b + c) ^ 2 * (b + c) * (a + b) + 2 * c * (a + b + c) ^ 2 * (b + c) * (c + a) - 3 * (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b) - (2 * a - b - c) ^ 2 * (b + c) * (c + a) * (a + b)) / (2 * (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      <;> ring
    rw [h13]
    have h15 : 2 * a * (a + b + c) ^ 2 * (c + a) * (a + b) + 2 * b * (a + b + c) ^ 2 * (b + c) * (a + b) + 2 * c * (a + b + c) ^ 2 * (b + c) * (c + a) - 3 * (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b) - (2 * a - b - c) ^ 2 * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h14 : (2 * a * (a + b + c) ^ 2 * (c + a) * (a + b) + 2 * b * (a + b + c) ^ 2 * (b + c) * (a + b) + 2 * c * (a + b + c) ^ 2 * (b + c) * (c + a) - 3 * (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b) - (2 * a - b - c) ^ 2 * (b + c) * (c + a) * (a + b)) / (2 * (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b)) ≥ 0 := by
      apply div_nonneg
      linarith [h15]
      positivity
    linarith
  linarith [h12]