import Mathlib

theorem inequalities_77348 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
    (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
    (3 * a + b + c) / (2 * a + 3 * b + 3 * c) ≥
    15 / 8 := by
  have h1 : 0 < 3 * a + 3 * b + 2 * c := by positivity
  have h2 : 0 < 3 * a + 2 * b + 3 * c := by positivity
  have h3 : 0 < 2 * a + 3 * b + 3 * c := by positivity
  have h4 : (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
      (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
      (3 * a + b + c) / (2 * a + 3 * b + 3 * c) - 15 / 8 ≥ 0 := by
    have h5 : (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
        (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
        (3 * a + b + c) / (2 * a + 3 * b + 3 * c) - 15 / 8 =
        ( (a + b + 3 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c) +
          (a + 3 * b + c) * (3 * a + 3 * b + 2 * c) * (2 * a + 3 * b + 3 * c) +
          (3 * a + b + c) * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) -
          15 / 8 * (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c) )
        / ( (3 * a + 3 * b + 2 * c) * (3 * a + 2 * b + 3 * c) * (2 * a + 3 * b + 3 * c) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    positivity
  linarith
  all_goals try positivity
  all_goals try linarith