import Mathlib

theorem inequalities_117840 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ (a - Real.sqrt (b * c)) / (a + 2 * (b + c)) + (b - Real.sqrt (c * a)) / (b + 2 * (c + a)) +
        (c - Real.sqrt (a * b)) / (c + 2 * (a + b)) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h10 : 0 < Real.sqrt (b * c) := by
    apply Real.sqrt_pos.mpr
    positivity

  have h11 : 0 < Real.sqrt (c * a) := by
    apply Real.sqrt_pos.mpr
    positivity

  have h12 : 0 < Real.sqrt (a * b) := by
    apply Real.sqrt_pos.mpr
    positivity

  have h3 : Real.sqrt (b * c) ≤ (b + c) / 2 := by
    nlinarith [Real.sqrt_nonneg (b * c), Real.sq_sqrt (show 0 ≤ (b * c : ℝ) by positivity), sq_nonneg (b - c)]

  have h4 : Real.sqrt (c * a) ≤ (c + a) / 2 := by
    nlinarith [Real.sqrt_nonneg (c * a), Real.sq_sqrt (show 0 ≤ (c * a : ℝ) by positivity), sq_nonneg (c - a)]

  have h5 : Real.sqrt (a * b) ≤ (a + b) / 2 := by
    nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by positivity), sq_nonneg (a - b)]

  have h6 : (a - Real.sqrt (b * c)) / (a + 2 * (b + c)) ≥ (a - (b + c) / 2) / (a + 2 * (b + c)) := by
    apply (div_le_div_right (by positivity)).mpr
    nlinarith [h3]

  have h7 : (b - Real.sqrt (c * a)) / (b + 2 * (c + a)) ≥ (b - (c + a) / 2) / (b + 2 * (c + a)) := by
    apply (div_le_div_right (by positivity)).mpr
    nlinarith [h4]

  have h8 : (c - Real.sqrt (a * b)) / (c + 2 * (a + b)) ≥ (c - (a + b) / 2) / (c + 2 * (a + b)) := by
    apply (div_le_div_right (by positivity)).mpr
    nlinarith [h5]

  have h9 : (a - Real.sqrt (b * c)) / (a + 2 * (b + c)) + (b - Real.sqrt (c * a)) / (b + 2 * (c + a)) + (c - Real.sqrt (a * b)) / (c + 2 * (a + b)) ≥ (a - (b + c) / 2) / (a + 2 * (b + c)) + (b - (c + a) / 2) / (b + 2 * (c + a)) + (c - (a + b) / 2) / (c + 2 * (a + b)) := by
    linarith [h6, h7, h8]

  have h10 : (a - (b + c) / 2) / (a + 2 * (b + c)) + (b - (c + a) / 2) / (b + 2 * (c + a)) + (c - (a + b) / 2) / (c + 2 * (a + b)) ≥ 0 := by
    have h100 : (a - (b + c) / 2) / (a + 2 * (b + c)) + (b - (c + a) / 2) / (b + 2 * (c + a)) + (c - (a + b) / 2) / (c + 2 * (a + b)) ≥ 0 := by
      have h101 : (a - (b + c) / 2) / (a + 2 * (b + c)) + (b - (c + a) / 2) / (b + 2 * (c + a)) + (c - (a + b) / 2) / (c + 2 * (a + b)) =
          ((2 * a - (b + c)) * (b + 2 * (c + a)) * (c + 2 * (a + b)) + (2 * b - (c + a)) * (a + 2 * (b + c)) * (c + 2 * (a + b)) + (2 * c - (a + b)) * (a + 2 * (b + c)) * (b + 2 * (c + a))) / (2 * (a + 2 * (b + c)) * (b + 2 * (c + a)) * (c + 2 * (a + b))) := by
        field_simp
        ring
      rw [h101]
      have h102 : (2 * a - (b + c)) * (b + 2 * (c + a)) * (c + 2 * (a + b)) + (2 * b - (c + a)) * (a + 2 * (b + c)) * (c + 2 * (a + b)) + (2 * c - (a + b)) * (a + 2 * (b + c)) * (b + 2 * (c + a)) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h103 : ((2 * a - (b + c)) * (b + 2 * (c + a)) * (c + 2 * (a + b)) + (2 * b - (c + a)) * (a + 2 * (b + c)) * (c + 2 * (a + b)) + (2 * c - (a + b)) * (a + 2 * (b + c)) * (b + 2 * (c + a))) / (2 * (a + 2 * (b + c)) * (b + 2 * (c + a)) * (c + 2 * (a + b))) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith

  linarith [h9, h10]