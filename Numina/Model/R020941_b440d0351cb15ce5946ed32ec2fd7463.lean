import Mathlib

theorem inequalities_89688 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 + 3 / (a + b + c) ≥ 6 / (a * b + b * c + c * a) := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 0 < (a + b + c) := by
    nlinarith [show 0 < a from ha, show 0 < b from hb, show 0 < c from hc]
  have h3 : 0 < (a * b + b * c + c * a) := by
    nlinarith [show 0 < a from ha, show 0 < b from hb, show 0 < c from hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h4 : 0 < (a + b + c) * (a * b + b * c + c * a) := by
    positivity
  have h5 : 1 + 3 / (a + b + c) - 6 / (a * b + b * c + c * a) ≥ 0 := by
    have h6 : 0 < (a + b + c) * (a * b + b * c + c * a) := by
      positivity
    have h55 : (1 + 3 / (a + b + c) - 6 / (a * b + b * c + c * a)) =
        ( (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b + b * c + c * a) - 6 * (a + b + c) ) / ( (a + b + c) * (a * b + b * c + c * a) ) := by
      field_simp
      <;> ring
    rw [h55] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b * c - 1), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith),
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * a from by nlinarith),
          mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith) ]
    all_goals positivity
  linarith