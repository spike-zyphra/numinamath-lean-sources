import Mathlib

theorem inequalities_46413 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) ≤ 1 / 2 := by
  have h1 : a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) ≤ 1 / 2 := by
    have h2 : (1 : ℝ) / 2 - (a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1)) ≥ 0 := by
      -- prove some postivity
      have h3 : (2 * a + 1) > 0 := by nlinarith
      have h4 : (3 * b + 1) > 0 := by nlinarith
      have h5 : (6 * c + 1) > 0 := by nlinarith
      have h : (1 : ℝ) / 2 - (a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1)) =
          ((1 / 2) * (2 * a + 1) * (3 * b + 1) * (6 * c + 1) - a * (3 * b + 1) * (6 * c + 1) - b * (2 * a + 1) * (6 * c + 1) - c * (2 * a + 1) * (3 * b + 1)) / ((2 * a + 1) * (3 * b + 1) * (6 * c + 1)) := by
        field_simp
        ring
      rw [h]
      apply div_nonneg
      · -- Prove numerator is non-negative
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 6),
          hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
      · -- Prove denominator is positive
        positivity
    linarith
  linarith [h1]