import Mathlib

theorem inequalities_27297 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 3 = a + b + c ∧ a + b + c ≤ 3 * a * b * c) :
    1 / Real.sqrt (2 * a + 1) + 1 / Real.sqrt (2 * b + 1) + 1 / Real.sqrt (2 * c + 1) ≤
    (3 / 2) ^ ((3 : ℝ) / 2) := by 
  have h1 : 3 = a + b + c := h.1
  have h2 : a + b + c ≤ 3 * a * b * c := h.2
  have h3 : a * b * c ≥ 1 := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h4 : a * b * c = 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have ha1 : a = 1 := by
    have h5 : (a - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have ha2 : a - 1 = 0 := by nlinarith
    linarith
  have hb1 : b = 1 := by
    have h5 : (b - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have hb2 : b - 1 = 0 := by nlinarith
    linarith
  have hc1 : c = 1 := by
    have h5 : (c - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have hc2 : c - 1 = 0 := by nlinarith
    linarith
  rw [ha1, hb1, hc1]
  have h6 : Real.sqrt (2 * (1 : ℝ) + 1) = Real.sqrt (3 : ℝ) := by norm_num
  rw [h6]
  have h7 : (1 / Real.sqrt (3 : ℝ) + 1 / Real.sqrt (3 : ℝ) + 1 / Real.sqrt (3 : ℝ)) ≤ (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) := by
    have h8 : (1 / Real.sqrt (3 : ℝ) + 1 / Real.sqrt (3 : ℝ) + 1 / Real.sqrt (3 : ℝ)) = Real.sqrt (3 : ℝ) := by
      have h9 : Real.sqrt (3 : ℝ) > 0 := by positivity
      field_simp
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [h8]
    have h10 : Real.sqrt (3 : ℝ) ≤ (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) := by
      have h12 : (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) ≥ Real.sqrt (3 : ℝ) := by
        have h14 : (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt ((3 / 2 : ℝ) ^ 3) := by
          have h15 : (3 / 2 : ℝ) ^ ((3 : ℝ) / 2) = ((3 / 2 : ℝ) ^ 3) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals
              norm_num
          have h16 : ((3 / 2 : ℝ) ^ 3) ^ (1 / 2 : ℝ) = Real.sqrt ((3 / 2 : ℝ) ^ 3) := by
            rw [Real.sqrt_eq_rpow]
          rw [h15, h16]
        rw [h14]
        have h17 : Real.sqrt ((3 / 2 : ℝ) ^ 3) ≥ Real.sqrt (3 : ℝ) := by
          apply Real.sqrt_le_sqrt
          norm_num
        linarith
      linarith
    linarith
  nlinarith