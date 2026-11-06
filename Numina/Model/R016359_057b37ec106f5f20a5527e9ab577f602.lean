import Mathlib

theorem inequalities_598707
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    1 ≤ a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) +
        d / (a + 2 * b + c) := by
  have h1 : 0 < b + 2 * c + d := by
    linarith
  have h2 : 0 < c + 2 * d + a := by
    linarith
  have h3 : 0 < d + 2 * a + b := by
    linarith
  have h4 : 0 < a + 2 * b + c := by
    linarith
  have h5 : a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c) - 1 ≥ 0 := by
    have h1' : 0 < (b + 2 * c + d) * (c + 2 * d + a) * (d + 2 * a + b) * (a + 2 * b + c) := by
      positivity
    have h5' : a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c) - 1 =
        ( (a * (c + 2 * d + a) * (d + 2 * a + b) * (a + 2 * b + c) ) +
          (b * (b + 2 * c + d) * (d + 2 * a + b) * (a + 2 * b + c) ) +
          (c * (b + 2 * c + d) * (c + 2 * d + a) * (a + 2 * b + c) ) +
          (d * (b + 2 * c + d) * (c + 2 * d + a) * (d + 2 * a + b) ) -
          ( (b + 2 * c + d) * (c + 2 * d + a) * (d + 2 * a + b) * (a + 2 * b + c) ) ) / ((b + 2 * c + d) * (c + 2 * d + a) * (d + 2 * a + b) * (a + 2 * b + c)) := by
      field_simp
      ring
    rw [h5']
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
      ]
    all_goals positivity
  linarith [h5]