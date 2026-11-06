import Mathlib

theorem inequalities_78980 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b + c) / 3 ≥ a / (a ^ 2 * b + 2) + b / (b ^ 2 * c + 2) + c / (c ^ 2 * a + 2) := by
  have h1 : a / (a ^ 2 * b + 2) = (a * c) / (a + 2 * c) := by 
    field_simp
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h2 : b / (b ^ 2 * c + 2) = (b * a) / (b + 2 * a) := by 
    field_simp
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h3 : c / (c ^ 2 * a + 2) = (c * b) / (c + 2 * b) := by 
    field_simp
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  rw [h1, h2, h3]
  have h4 : 0 < a + b + c := by
    linarith [ha, hb, hc]
  have h5 : (a + b + c) / 3 ≥ (a * c) / (a + 2 * c) + (b * a) / (b + 2 * a) + (c * b) / (c + 2 * b) := by
    have h6 : 0 < a + 2 * c := by
      nlinarith
    have h7 : 0 < b + 2 * a := by
      nlinarith
    have h8 : 0 < c + 2 * b := by
      nlinarith
    have h9 : (a + b + c) / 3 - (a * c) / (a + 2 * c) - (b * a) / (b + 2 * a) - (c * b) / (c + 2 * b) ≥ 0 := by
      have pos1 : (a + 2 * c) * (b + 2 * a) * (c + 2 * b) > 0 := by positivity
      have eq : (a + b + c) / 3 - (a * c) / (a + 2 * c) - (b * a) / (b + 2 * a) - (c * b) / (c + 2 * b) =
          ((a + b + c) / 3 * ((a + 2 * c) * (b + 2 * a) * (c + 2 * b)) -
          (a * c) * ((b + 2 * a) * (c + 2 * b)) -
          (b * a) * ((a + 2 * c) * (c + 2 * b)) -
          (c * b) * ((a + 2 * c) * (b + 2 * a))
          ) / ((a + 2 * c) * (b + 2 * a) * (c + 2 * b)) := by
        field_simp
        <;> ring
      rw [eq]
      have eq2 : (a + b + c) / 3 * ((a + 2 * c) * (b + 2 * a) * (c + 2 * b)) -
          (a * c) * ((b + 2 * a) * (c + 2 * b)) -
          (b * a) * ((a + 2 * c) * (c + 2 * b)) -
          (c * b) * ((a + 2 * c) * (b + 2 * a)
          ) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      apply div_nonneg eq2 (by positivity)
    linarith
  linarith