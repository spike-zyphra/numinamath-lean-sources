import Mathlib

theorem algebra_297207 (x : ℝ) (hx : x > 1 / 4) :
    Real.sqrt (x + 1 / 2 + 1 / 2 * Real.sqrt (4 * x + 1)) -
    Real.sqrt (x + 1 / 2 - 1 / 2 * Real.sqrt (4 * x + 1)) = 1 := by

  have h1 : Real.sqrt (4 * x + 1) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h11 : Real.sqrt (4 * x + 1) > 1 := by
    have h2 : Real.sqrt (4 * x + 1) > 1 := by
      have h3 : 4 * x + 1 > 1 := by linarith
      have h4 : Real.sqrt (4 * x + 1) > Real.sqrt (1 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals linarith
      have h5 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith [h4, h5]
    linarith

  have h2 : x + 1 / 2 + 1 / 2 * Real.sqrt (4 * x + 1) = ((Real.sqrt (4 * x + 1) + 1) / 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (show 0 ≤ (4 * x + 1 : ℝ) by linarith)]

  have h3 : x + 1 / 2 - 1 / 2 * Real.sqrt (4 * x + 1) = ((Real.sqrt (4 * x + 1) - 1) / 2) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (show 0 ≤ (4 * x + 1 : ℝ) by linarith)]

  have h4 : Real.sqrt (x + 1 / 2 + 1 / 2 * Real.sqrt (4 * x + 1)) = (Real.sqrt (4 * x + 1) + 1) / 2 := by
    rw [h2]
    have h5 : 0 ≤ (Real.sqrt (4 * x + 1) + 1) / 2 := by
      have h6 : Real.sqrt (4 * x + 1) ≥ 0 := Real.sqrt_nonneg (4 * x + 1)
      linarith
    rw [Real.sqrt_sq (by
      have h7 : Real.sqrt (4 * x + 1) + 1 ≥ 0 := by
        linarith [Real.sqrt_nonneg (4 * x + 1)]
      have h8 : (Real.sqrt (4 * x + 1) + 1) / 2 ≥ 0 := by linarith
      linarith
    )]

  have h6 : Real.sqrt (x + 1 / 2 - 1 / 2 * Real.sqrt (4 * x + 1)) = (Real.sqrt (4 * x + 1) - 1) / 2 := by
    rw [h3]
    have h5 : 0 ≤ (Real.sqrt (4 * x + 1) - 1) / 2 := by
      have h6 : Real.sqrt (4 * x + 1) ≥ 1 := by linarith
      linarith
    rw [Real.sqrt_sq (by
      have h7 : Real.sqrt (4 * x + 1) - 1 ≥ 0 := by
        linarith [Real.sqrt_nonneg (4 * x + 1), h11]
      have h8 : (Real.sqrt (4 * x + 1) - 1) / 2 ≥ 0 := by linarith
      linarith
    )]

  rw [h4, h6]
  have h7 : Real.sqrt (4 * x + 1) > 1 := h11
  nlinarith