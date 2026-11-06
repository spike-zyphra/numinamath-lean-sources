import Mathlib

theorem inequalities_48138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / a + 1 / b + 1 / c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h3 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / a + 1 / b + 1 / c) = 
      (a^2 * c + b^2 * a + c^2 * b)^2 / (a^2 * b^2 * c^2) - (a + b + c) * (b * c + a * c + a * b) / (a * b * c) := by
      field_simp [hb.ne.symm, hc.ne.symm, ha.ne.symm]
      ring
    rw [h3] at *
    have h4 : (a^2 * c + b^2 * a + c^2 * b)^2 ≥ (a + b + c) * (b * c + a * c + a * b) * (a * b * c) := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
                sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
                sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
                mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
                mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)
                ]
    have h5 : (a^2 * c + b^2 * a + c^2 * b)^2 / (a^2 * b^2 * c^2) ≥ (a + b + c) * (b * c + a * c + a * b) / (a * b * c) := by
      have h6 : 0 < a^2 * b^2 * c^2 := by positivity
      have h7 : (a^2 * c + b^2 * a + c^2 * b)^2 ≥ (a + b + c) * (b * c + a * c + a * b) * (a * b * c) := h4
      have h8 : (a^2 * c + b^2 * a + c^2 * b)^2 / (a^2 * b^2 * c^2) ≥ (a + b + c) * (b * c + a * c + a * b) / (a * b * c) := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      exact h8
    linarith
  linarith