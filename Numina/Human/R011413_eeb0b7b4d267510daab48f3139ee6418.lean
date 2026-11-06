import Mathlib

theorem inequalities_32331 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    a * c / (c ^ 5 + a ^ 5 + a * c) ≤ 1 := by
  -- prove `a ^ 5 + b ^ 5 ≥ a ^ 2 * b ^ 2 * (a + b)`
  have h1 : a ^ 5 + b ^ 5 ≥ a ^ 2 * b ^ 2 * (a + b) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b - 1), sq_nonneg (a - b),
              sq_nonneg (a + b), sq_nonneg (a ^ 2 + a * b + b ^ 2),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  -- prove `b ^ 5 + c ^ 5 ≥ b ^ 2 * c ^ 2 * (b + c) `
  have h2 : b ^ 5 + c ^ 5 ≥ b ^ 2 * c ^ 2 * (b + c) := by
    nlinarith [sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b * c - 1), sq_nonneg (b - c),
              sq_nonneg (b + c), sq_nonneg (b ^ 2 + b * c + c ^ 2),
              mul_pos hb hc, mul_pos ha hb, mul_pos ha hc]
  -- prove `c ^ 5 + a ^ 5 ≥ c ^ 2 * a ^ 2 * (c + a)`
  have h3 : c ^ 5 + a ^ 5 ≥ c ^ 2 * a ^ 2 * (c + a) := by
    nlinarith [sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (c * a - 1), sq_nonneg (c - a),
              sq_nonneg (c + a), sq_nonneg (c ^ 2 + c * a + a ^ 2),
              mul_pos ha hc, mul_pos ha hb, mul_pos hb hc]
  have h4 : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    have h4_pos1 : 0 < a ^ 5 + b ^ 5 + a * b := by
      nlinarith [pow_pos ha 5, pow_pos hb 5, mul_pos ha hb]
    have h4_pos2 : 0 < a + b + c := by nlinarith
    have h4_num : a * b * (a + b + c) ≤ c * (a ^ 5 + b ^ 5 + a * b) := by
      nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    have h4' : a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith
    exact h4'
  -- prove `b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) `
  have h5 : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
    have h5_pos1 : 0 < b ^ 5 + c ^ 5 + b * c := by
      nlinarith [pow_pos hb 5, pow_pos hc 5, mul_pos hb hc]
    have h5_pos2 : 0 < a + b + c := by nlinarith
    have h5_num : b * c * (a + b + c) ≤ a * (b ^ 5 + c ^ 5 + b * c) := by
      nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    have h5' : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith
    exact h5'
  have h6 : a * c / (c ^ 5 + a ^ 5 + a * c) ≤ b / (a + b + c) := by
    have h6_pos1 : 0 < c ^ 5 + a ^ 5 + a * c := by
      nlinarith [pow_pos hc 5, pow_pos ha 5, mul_pos ha hc]
    have h6_pos2 : 0 < a + b + c := by nlinarith
    have h6_num : a * c * (a + b + c) ≤ b * (c ^ 5 + a ^ 5 + a * c) := by
      nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    have h6' : a * c / (c ^ 5 + a ^ 5 + a * c) ≤ b / (a + b + c) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith
    exact h6'
  have h7 : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + a * c / (c ^ 5 + a ^ 5 + a * c) ≤ 1 := by
    have h7_pos : 0 < a + b + c := by nlinarith
    have h7_combined : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + a * c / (c ^ 5 + a ^ 5 + a * c) ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by
      linarith [h4, h5, h6]
    have h7_simplified : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
      have h7_simplified1 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = (a + b + c) / (a + b + c) := by
        field_simp [ne_of_gt h7_pos]
        ring
      rw [h7_simplified1]
      have h7_simplified2 : (a + b + c) / (a + b + c) = 1 := by
        rw [div_self]
        linarith
      exact h7_simplified2
    linarith [h7_combined, h7_simplified]
  linarith [h7]