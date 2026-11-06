import Mathlib

open Real

theorem inequalities_224622 (k : ℝ) :
    (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
      a * b + b * c + c * a + k * (1 / a + 1 / b + 1 / c) ≥ 9) ↔
    k ≥ 2 := by
  constructor
  · -- Forward direction: if the inequality holds for all positive a, b, c, then k ≥ 2.
    intro h
    have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1
    linarith
  · -- Backward direction: if k ≥ 2, then the inequality holds for all positive a, b, c.
    intro hk a b c ha hb hc
    have h2 : a * b + 1 / a + 1 / b ≥ 3 := by
      have h3 : a * b + 1 / a + 1 / b - 3 ≥ 0 := by
        have h4 : a * b + 1 / a + 1 / b - 3 = (a ^ 2 * b ^ 2 + a + b - 3 * a * b) / (a * b) := by
          field_simp
          ring
        rw [h4]
        have h5 : a ^ 2 * b ^ 2 + a + b - 3 * a * b ≥ 0 := by
          nlinarith [sq_nonneg (a ^ 2 * b ^ 2 - a * b), sq_nonneg (a - b), sq_nonneg (a * b - 1), mul_pos ha hb, sq_nonneg (a * b), sq_nonneg (a - 1), sq_nonneg (b - 1)]
        apply div_nonneg
        nlinarith
        nlinarith [mul_pos ha hb]
      nlinarith
    have h3 : b * c + 1 / b + 1 / c ≥ 3 := by
      have h4 : b * c + 1 / b + 1 / c - 3 ≥ 0 := by
        have h5 : b * c + 1 / b + 1 / c - 3 = (b ^ 2 * c ^ 2 + b + c - 3 * b * c) / (b * c) := by
          field_simp
          ring
        rw [h5]
        have h6 : b ^ 2 * c ^ 2 + b + c - 3 * b * c ≥ 0 := by
          nlinarith [sq_nonneg (b ^ 2 * c ^ 2 - b * c), sq_nonneg (b - c), sq_nonneg (b * c - 1), mul_pos hb hc, sq_nonneg (b * c), sq_nonneg (b - 1), sq_nonneg (c - 1)]
        apply div_nonneg
        nlinarith
        nlinarith [mul_pos hb hc]
      nlinarith
    have h4 : c * a + 1 / c + 1 / a ≥ 3 := by
      have h5 : c * a + 1 / c + 1 / a - 3 ≥ 0 := by
        have h6 : c * a + 1 / c + 1 / a - 3 = (c ^ 2 * a ^ 2 + c + a - 3 * c * a) / (c * a) := by
          field_simp
          ring
        rw [h6]
        have h7 : c ^ 2 * a ^ 2 + c + a - 3 * c * a ≥ 0 := by
          nlinarith [sq_nonneg (c ^ 2 * a ^ 2 - c * a), sq_nonneg (c - a), sq_nonneg (c * a - 1), mul_pos hc ha, sq_nonneg (c * a), sq_nonneg (c - 1), sq_nonneg (a - 1)]
        apply div_nonneg
        nlinarith
        nlinarith [mul_pos hc ha]
      nlinarith
    have h5 : (a * b + b * c + c * a) + 2 * (1 / a + 1 / b + 1 / c) ≥ 9 := by
      nlinarith [h2, h3, h4]
    have h7 : k * (1 / a + 1 / b + 1 / c) ≥ 2 * (1 / a + 1 / b + 1 / c) := by
      have h8 : (k - (2 : ℝ)) * (1 / a + 1 / b + 1 / c) ≥ 0 := by
        have h9 : 1 / a + 1 / b + 1 / c > 0 := by
          have h10 : 1 / a > 0 := by
            apply one_div_pos.mpr
            exact ha
          have h11 : 1 / b > 0 := by
            apply one_div_pos.mpr
            exact hb
          have h12 : 1 / c > 0 := by
            apply one_div_pos.mpr
            exact hc
          linarith
        have h10 : k - (2 : ℝ) ≥ 0 := by
          linarith
        apply mul_nonneg
        linarith
        linarith
      linarith
    nlinarith [h5, h7, mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ (a * b + b * c + c * a) by positivity)]