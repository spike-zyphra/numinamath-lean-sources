import Mathlib

open Real

theorem inequalities_597841 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hle : a ≤ b ∧ b ≤ c) (h : a + b + c = 3) :
    sqrt (3 * a^2 + 1) + sqrt (5 * a^2 + 3 * b^2 + 1) +
    sqrt (7 * a^2 + 5 * b^2 + 3 * c^2 + 1) ≤ 9 := by

  have h1 : sqrt (3 * a ^ 2 + 1) ≤ a + 1 := by
    have h2 : (3 * a ^ 2 + 1 : ℝ) ≤ (a + 1) ^ 2 := by
      nlinarith
    have h3 : Real.sqrt (3 * a ^ 2 + 1) ≤ Real.sqrt ((a + 1) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h4 : Real.sqrt ((a + 1) ^ 2) = (a + 1) := by
      rw [Real.sqrt_sq]
      linarith
    linarith

  have h2 : sqrt (5 * a ^ 2 + 3 * b ^ 2 + 1) ≤ b + 2 := by
    have h3 : (5 * a ^ 2 + 3 * b ^ 2 + 1 : ℝ) ≤ (b + 2) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), hle.1, hle.2, h]
    have h4 : Real.sqrt (5 * a ^ 2 + 3 * b ^ 2 + 1) ≤ Real.sqrt ((b + 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h5 : Real.sqrt ((b + 2) ^ 2) = (b + 2) := by
      rw [Real.sqrt_sq]
      linarith
    linarith

  have h3 : sqrt (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1) ≤ c + 3 := by
    have h4 : (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1 : ℝ) ≤ (c + 3) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        hle.1, hle.2, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    have h5 : Real.sqrt (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1) ≤ Real.sqrt ((c + 3) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h6 : Real.sqrt ((c + 3) ^ 2) = (c + 3) := by
      rw [Real.sqrt_sq]
      linarith
    linarith

  have h4 : sqrt (3 * a^2 + 1) + sqrt (5 * a^2 + 3 * b^2 + 1) +
    sqrt (7 * a^2 + 5 * b^2 + 3 * c^2 + 1) ≤ (a + 1) + (b + 2) + (c + 3) := by
    linarith [h1, h2, h3]

  have h5 : (a + 1 : ℝ) + (b + 2) + (c + 3) = 9 := by
    nlinarith [h]

  linarith [h4, h5]