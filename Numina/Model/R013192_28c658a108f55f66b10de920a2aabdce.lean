import Mathlib

theorem algebra_289103 (a b c : ℝ) (h : a + b + c = 12) :
    Real.sqrt (a^2 + 1) + Real.sqrt (b^2 + 9) + Real.sqrt (c^2 + 25) ≥ 15 := by
  have h1 : Real.sqrt (a^2 + 1) ≥ (4/5) * a + 3/5 := by
    have h1 : ((4/5) * a + 3/5) ^ 2 ≤ (a ^ 2 + 1 : ℝ) := by
      nlinarith [sq_nonneg (3 * a - 4)]
    have h2 : (4/5 * a + 3/5) ≤ Real.sqrt (a^2 + 1) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have h2 : Real.sqrt (b^2 + 9) ≥ (4/5) * b + 9/5 := by
    have h1 : ((4/5) * b + 9/5) ^ 2 ≤ (b ^ 2 + 9 : ℝ) := by
      nlinarith [sq_nonneg (b - 4)]
    have h2 : (4/5 * b + 9/5) ≤ Real.sqrt (b^2 + 9) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have h3 : Real.sqrt (c^2 + 25) ≥ (4/5) * c + 3 := by
    have h1 : ((4/5) * c + 3) ^ 2 ≤ (c ^ 2 + 25 : ℝ) := by
      nlinarith [sq_nonneg (c - 20/3)]
    have h2 : (4/5 * c + 3) ≤ Real.sqrt (c^2 + 25) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have h7 : Real.sqrt (a^2 + 1) + Real.sqrt (b^2 + 9) + Real.sqrt (c^2 + 25) ≥ (4/5) * a + (3/5) + (4/5) * b + (9/5) + (4/5) * c + 3 := by
    linarith [h1, h2, h3]
  have h8 : (4/5) * a + (3/5) + (4/5) * b + (9/5) + (4/5) * c + 3 = 15 := by
    have h9 : a + b + c = 12 := h
    linarith
  linarith [h7, h8]