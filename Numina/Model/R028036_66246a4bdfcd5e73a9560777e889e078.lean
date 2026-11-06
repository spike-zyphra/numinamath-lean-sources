import Mathlib

theorem inequalities_598453 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * a / ((b + c) * (2 * a + b + c)) +
    (b + c) * b / ((c + a) * (2 * b + c + a)) +
    (c + a) * c / ((a + b) * (2 * c + a + b)) ≥ 3 / 4 := by

  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc

  have h1 : 0 < (b + c) * (2 * a + b + c) := by positivity
  have h2 : 0 < (c + a) * (2 * b + c + a) := by positivity
  have h3 : 0 < (a + b) * (2 * c + a + b) := by positivity

  have h4 : (a + b) * a / ((b + c) * (2 * a + b + c)) +
      (b + c) * b / ((c + a) * (2 * b + c + a)) +
      (c + a) * c / ((a + b) * (2 * c + a + b)) - 3 / 4 ≥ 0 := by
    have h5 : 0 < (b + c) * (2 * a + b + c) * (c + a) * (2 * b + c + a) * (a + b) * (2 * c + a + b) := by positivity

    have h6 : ( (a + b) * a / ((b + c) * (2 * a + b + c)) +
        (b + c) * b / ((c + a) * (2 * b + c + a)) +
        (c + a) * c / ((a + b) * (2 * c + a + b)) - 3 / 4 ) =
        ( (a + b) * a * (c + a) * (2 * b + c + a) * (a + b) * (2 * c + a + b) +
        (b + c) * b * (b + c) * (2 * a + b + c) * (a + b) * (2 * c + a + b) +
        (c + a) * c * (b + c) * (2 * a + b + c) * (c + a) * (2 * b + c + a) - 3 / 4 * (b + c) * (2 * a + b + c) * (c + a) * (2 * b + c + a) * (a + b) * (2 * c + a + b) ) / ( (b + c) * (2 * a + b + c) * (c + a) * (2 * b + c + a) * (a + b) * (2 * c + a + b) ) := by
      field_simp
      ring

    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    all_goals positivity

  linarith