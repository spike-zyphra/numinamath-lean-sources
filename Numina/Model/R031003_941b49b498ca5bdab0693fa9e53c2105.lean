import Mathlib

open Real

theorem inequalities_607510 (a : ℝ) (ha : 0 ≤ a) : a ^ 3 + 2 ≥ a ^ 2 + 2 * √a := by
  have h1 : (√a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h2 : 0 ≤ √a := by positivity
  by_cases h3 : √a ≥ 1
  · -- Case where √a ≥ 1, so a ≥ 1.
    have ha1 : a ≥ 1 := by
      have h4 : √a ≥ 1 := h3
      have h5 : (√a) ^ 2 ≥ (1 : ℝ) ^ 2 := by
        nlinarith [h4, Real.sqrt_nonneg a]
      nlinarith [h1, h4, sq_nonneg (√a - 1)]
    have h4 : a ^ 2 * (a - 1) ≥ 2 * (√a - 1) := by
      have h5 : √a ≥ 1 := h3
      have h6 : a ≥ 1 := ha1
      nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (√a - 1), sq_nonneg (a - 1), sq_nonneg ((√a) ^ 2 - 1),
        Real.sqrt_nonneg a, sq_nonneg (a - (√a : ℝ)), Real.sq_sqrt (show 0 ≤ a by linarith)]
    nlinarith [Real.sqrt_nonneg a, sq_nonneg (√a ^ 2 - 1), sq_nonneg (a - 1)]
  · -- Case where √a < 1, so 0 ≤ a < 1.
    have h4 : √a < 1 := by
      linarith
    have ha1 : a < 1 := by
      nlinarith [h4, Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ a by linarith)]
    have h4 : a ^ 2 * (a - 1) ≥ 2 * (√a - 1) := by
      have h5 : √a < 1 := h4
      have h6 : a < 1 := ha1
      nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (√a - 1), sq_nonneg (a - 1), sq_nonneg ((√a) ^ 2 - 1),
        Real.sqrt_nonneg a, sq_nonneg (a - (√a : ℝ)), Real.sq_sqrt (show 0 ≤ a by linarith)]
    nlinarith [Real.sqrt_nonneg a, sq_nonneg (√a ^ 2 - 1), sq_nonneg (a - 1)]