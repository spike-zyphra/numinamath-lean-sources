import Mathlib

open Real

theorem inequalities_959 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = Real.sqrt 3) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ ((1 : ℝ) / 3) ≥
    2 * (a * b + b * c + c * a) + 1 := by
  have h1 : (a + b + c : ℝ) = Real.sqrt 3 := h

  have h2 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
      sq_nonneg (a + b + c - 2 * Real.sqrt 3 / 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h3 : (a ^ 2 + b ^ 2 + c ^ 2 : ℝ) ≥ 1 := h2

  have h4 : (a ^ 2 + b ^ 2 + c ^ 2 : ℝ) ^ ((1 : ℝ) / 3) ≥ (1 : ℝ) := by
    have h5 : (a ^ 2 + b ^ 2 + c ^ 2 : ℝ) ≥ (1 : ℝ) := by linarith
    have h6 : (a ^ 2 + b ^ 2 + c ^ 2 : ℝ) ^ ((1 : ℝ) / 3) ≥ (1 : ℝ) := by
      have h7 : (a ^ 2 + b ^ 2 + c ^ 2 : ℝ) ^ ((1 : ℝ) / 3) ≥ ((1 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_le_rpow
        linarith
        all_goals linarith
      have h8 : ((1 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
        rw [show ((1 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = (1 ^ (1 / 3 : ℝ)) by norm_num]
        rw [one_rpow]
      nlinarith [h7, h8]
    linarith

  have h7 : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ ((1 : ℝ) / 3) ≥ 3 := by
    nlinarith [h4]

  have h8 : 2 * (a * b + b * c + c * a) + 1 ≤ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), h,
      h2, h1, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  nlinarith [h7, h8]