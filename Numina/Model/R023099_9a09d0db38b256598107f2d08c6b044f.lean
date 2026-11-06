import Mathlib

theorem inequalities_598586
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) := by
  have h1 : 0 < (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) := by
    positivity

  have h2 : 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1 ≥ 0 := by
    have pos1 : 0 < 1 + 2 * a * b := by
      nlinarith [mul_pos ha hb]
    have pos2 : 0 < 1 + 2 * b * c := by
      nlinarith [mul_pos hb hc]
    have pos3 : 0 < 1 + 2 * c * a := by
      nlinarith [mul_pos hc ha]
    have h' : 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) - 1 =
              ( (1 + 2 * b * c) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * c * a) + (1 + 2 * a * b) * (1 + 2 * b * c) - (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) / ( (1 + 2 * a * b) * (1 + 2 * b * c) * (1 + 2 * c * a) ) := by
      field_simp
      <;> ring
    rw [h']
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              mul_pos ha hb, mul_pos hb hc, mul_pos hc ha
            ]
    all_goals
      positivity

  linarith