import Mathlib

theorem inequalities_128586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ∧
    2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≤ 1 / a + 1 / b + 1 / c := by
  constructor
  · -- Proof of 9/(a+b+c) ≤ 2/(a+b) + 2/(b+c) + 2/(c+a)
    have h1 : 0 < a + b := by linarith
    have h2 : 0 < b + c := by linarith
    have h3 : 0 < c + a := by linarith
    have h4 : 0 < a + b + c := by linarith
    have h5 : 9 / (a + b + c) - (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) ≤ 0 := by
      have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
      have pos2 : 0 < (a + b + c) * (a + b) * (b + c) * (c + a) := by positivity
      have h6 : 9 / (a + b + c) - (2 / (a + b) + 2 / (b + c) + 2 / (c + a)) =
          (9 * ((a + b) * (b + c) * (c + a)) - 2 * ( (b + c) * (c + a) * (a + b + c) + (a + b) * (c + a) * (a + b + c) + (a + b) * (b + c) * (a + b + c) )) / ((a + b + c) * ((a + b) * (b + c) * (c + a)) ) := by
        field_simp
        ring
      rw [h6]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity)]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith
  · -- Proof of 2/(a+b) + 2/(b+c) + 2/(c+a) ≤ 1/a + 1/b + 1/c
    have h1 : 0 < a := by linarith
    have h2 : 0 < b := by linarith
    have h3 : 0 < c := by linarith
    have h4 : 0 < a + b := by linarith
    have h5 : 0 < b + c := by linarith
    have h6 : 0 < c + a := by linarith
    have h7 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - (1 / a + 1 / b + 1 / c) ≤ 0 := by
      have pos1 : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
      have h8 : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) - (1 / a + 1 / b + 1 / c) =
          (2 * ( a * b * c * ( (b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c) )) - (1 * ( (a + b) * (b + c) * (c + a) * (a * b + b * c + c * a) ) ) ) / ( a * b * c * (a + b) * (b + c) * (c + a) ) := by
        field_simp
        ring
      rw [h8]
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is ≤ 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity),
          mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity),
          mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity)]
      · -- Show that the denominator is ≥ 0
        positivity
    linarith