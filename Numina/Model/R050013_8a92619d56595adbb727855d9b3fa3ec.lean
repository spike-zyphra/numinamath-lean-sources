import Mathlib

theorem algebra_598 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ |b|) (h : 3 * √ a + 5 * |b| = 7) :
    2 * √ a - 3 * |b| ≤ 14 / 3 ∧ 2 * √ a - 3 * |b| ≥ -21 / 5 := by

  have h1 : 0 ≤ √ a := by positivity
  have h2 : 0 ≤ |b| := by linarith [hb]

  constructor
  · -- Show upper bound 14/3
    nlinarith [sq_nonneg (√ a - 7 / 3), sq_nonneg (|b| - 0), sq_nonneg (√ a * 5 - 7 * 3), sq_nonneg (|b| * 3 - 0),
      Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith), hb, mul_nonneg (Real.sqrt_nonneg a) hb]

  · -- Show lower bound -21/5
    nlinarith [sq_nonneg (√ a - 0), sq_nonneg (|b| - 7 / 5), sq_nonneg (√ a * 5 - 0), sq_nonneg (|b| * 3 - 7 * 3 / 5),
      Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith), hb, mul_nonneg (Real.sqrt_nonneg a) hb]