import Mathlib

theorem inequalities_66106 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by

  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h2 : 0 < a + b := by linarith
    have h3 : 0 < a + c := by linarith
    have h4 : 0 < b + c := by linarith

    -- define the fraction expression and multiply by denominators to move to numerator
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
      (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      <;> ring
    rw [h5]
    apply div_nonneg
    -- positive and negative terms
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    -- denominators are positive products
    positivity

  -- After proving A - b >= 0, get A >= b
  linarith