import Mathlib

theorem inequalities_83491 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 4 ≤ a ^ 2 / ((a + b) * (a + c)) + b ^ 2 / ((b + c) * (b + a)) +
    c ^ 2 / ((c + a) * (c + b)) := by
  have h1 : 0 < (a + b) * (a + c) := by
    positivity
  have h2 : 0 < (b + c) * (b + a) := by
    positivity
  have h3 : 0 < (c + a) * (c + b) := by
    positivity
  have h4 : 0 < (a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b) := by
    positivity
  have h5 : a ^ 2 / ((a + b) * (a + c)) + b ^ 2 / ((b + c) * (b + a)) + c ^ 2 / ((c + a) * (c + b)) - 3 / 4 ≥ 0 := by
    have pos1 : 0 < (a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b) := by positivity
    have h : a ^ 2 / ((a + b) * (a + c)) + b ^ 2 / ((b + c) * (b + a)) + c ^ 2 / ((c + a) * (c + b)) - 3 / 4 =
        ( (a ^ 2 * (b + c) * (b + a) * (c + a) * (c + b) +
              b ^ 2 * (a + b) * (a + c) * (c + a) * (c + b) +
              c ^ 2 * (a + b) * (a + c) * (b + c) * (b + a) - 3 / 4 * ((a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b)) ) / ((a + b) * (a + c) * (b + c) * (b + a) * (c + a) * (c + b)) ) := by
        field_simp
        ring
    rw [h] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    all_goals positivity
  linarith [h5]