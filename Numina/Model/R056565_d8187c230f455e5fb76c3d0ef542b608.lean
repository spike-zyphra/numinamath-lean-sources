import Mathlib

theorem inequalities_291089 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ≥ 69 / 4 := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h4 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 ≥ 0 := by
    have h5 : 0 < (1 + a) * (1 + b) * (1 + c) := by
      positivity
    have eq : ((7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4) =
        ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b) - 69 / 4 * (1 + a) * (1 + b) * (1 + c)) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp [h1, h2, h3]
      ring
    rw [eq]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
      h, sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4)
    ]
    positivity
  linarith