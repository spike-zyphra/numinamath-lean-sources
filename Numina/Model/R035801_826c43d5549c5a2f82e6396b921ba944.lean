import Mathlib

theorem inequalities_598969 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hle : a ≤ b ∧ b ≤ c) (hsum : a + b + c = 3) :
    Real.sqrt (3 * a ^ 2 + 1) + Real.sqrt (5 * a ^ 2 + 3 * b ^ 2 + 1) +
    Real.sqrt (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1) ≤ 9 := by

  have h1 : a ≤ 1 := by
    nlinarith [hle.1, hle.2, hsum]

  have h2 : c ≥ 1 := by
    nlinarith [hle.1, hle.2, hsum]

  have h3 : Real.sqrt (3 * a ^ 2 + 1) ≤ a + 1 := by
    have h4 : 3 * a ^ 2 + 1 ≤ (a + 1) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), h1]
    have h5 : Real.sqrt (3 * a ^ 2 + 1) ≤ Real.sqrt ((a + 1) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h6 : Real.sqrt ((a + 1) ^ 2) = a + 1 := by
      rw [Real.sqrt_sq (show 0 ≤ (a + 1 : ℝ) by linarith)]
    linarith [h5, h6]

  have h4 : Real.sqrt (5 * a ^ 2 + 3 * b ^ 2 + 1) ≤ b + 2 := by
    have h5 : 5 * a ^ 2 + 3 * b ^ 2 + 1 ≤ (b + 2) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), hle.1, hle.2, hsum]
    have h6 : Real.sqrt (5 * a ^ 2 + 3 * b ^ 2 + 1) ≤ Real.sqrt ((b + 2) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have  h7 : Real.sqrt ((b + 2) ^ 2) = b + 2 := by
      rw [Real.sqrt_sq (show 0 ≤ (b + 2 : ℝ) by linarith)]
    linarith [h6, h7]

  have h5 : Real.sqrt (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1) ≤ c + 3 := by
    have h6 : 7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1 ≤ (c + 3) ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), hle.1, hle.2, hsum]
    have h7 : Real.sqrt (7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + 1) ≤ Real.sqrt ((c + 3) ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h8 : Real.sqrt ((c + 3) ^ 2) = c + 3 := by
      rw [Real.sqrt_sq (show 0 ≤ (c + 3 : ℝ) by linarith)]
    linarith [h7, h8]

  nlinarith [h3, h4, h5, hsum]