import Mathlib

theorem inequalities_605779 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c + a * b + b * c + c * a + a * b * c = 7) :
    Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) + Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ 6 := by

  have h1 : Real.sqrt (a ^ 2 + b ^ 2 + 2) ≥ (a + b + 2) / 2 := by
    have h2 : a ^ 2 + b ^ 2 + 2 ≥ ((a + b + 2) / 2) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]
    have h3 : Real.sqrt (a ^ 2 + b ^ 2 + 2) ≥ Real.sqrt (((a + b + 2) / 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h4 : Real.sqrt (((a + b + 2) / 2) ^ 2) = (a + b + 2) / 2 := by
      rw [Real.sqrt_sq]
      positivity
    linarith [h3, h4]

  have h2 : Real.sqrt (b ^ 2 + c ^ 2 + 2) ≥ (b + c + 2) / 2 := by
    have h3 : b ^ 2 + c ^ 2 + 2 ≥ ((b + c + 2) / 2) ^ 2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 2)]
    have h4 : Real.sqrt (b ^ 2 + c ^ 2 + 2) ≥ Real.sqrt (((b + c + 2) / 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h5 : Real.sqrt (((b + c + 2) / 2) ^ 2) = (b + c + 2) / 2 := by
      rw [Real.sqrt_sq]
      positivity
    linarith [h4, h5]

  have h3 : Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ (c + a + 2) / 2 := by
    have h4 : c ^ 2 + a ^ 2 + 2 ≥ ((c + a + 2) / 2) ^ 2 := by
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a - 2)]
    have h5 : Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ Real.sqrt (((c + a + 2) / 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h6 : Real.sqrt (((c + a + 2) / 2) ^ 2) = (c + a + 2) / 2 := by
      rw [Real.sqrt_sq]
      positivity
    linarith [h5, h6]

  have h5 : a + b + c ≥ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h7 : Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) + Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ a + b + c + 3 := by
    linarith [h1, h2, h3]

  linarith [h7, h5]