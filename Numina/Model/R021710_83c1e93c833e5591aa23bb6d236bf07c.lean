import Mathlib

theorem algebra_322719 (x : ℝ) (hx : x > 1 / 4) :
    Real.sqrt (x + 1 / 2 + Real.sqrt (4 * x + 1) / 2) -
    Real.sqrt (x + 1 / 2 - Real.sqrt (4 * x + 1) / 2) = 1 := by

  have h1 : 0 < 4 * x + 1 := by
    linarith

  have h2 : Real.sqrt (4 * x + 1) ≥ 0 := by
    apply Real.sqrt_nonneg

  have h3 : Real.sqrt (4 * x + 1) ^ 2 = 4 * x + 1 := by
    exact Real.sq_sqrt (by linarith)

  have h4 : Real.sqrt (x + 1 / 2 + Real.sqrt (4 * x + 1) / 2) = (Real.sqrt (4 * x + 1) + 1) / 2 := by
    have h4 : (Real.sqrt (4 * x + 1) + 1) / 2 ≥ 0 := by
      linarith [Real.sqrt_nonneg (4 * x + 1), Real.sqrt_nonneg (4 * x + 1)]

    have h5 : ((Real.sqrt (4 * x + 1) + 1) / 2) ^ 2 = x + 1 / 2 + Real.sqrt (4 * x + 1) / 2 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (by linarith : (4 * x + 1 : ℝ) ≥ 0)]

    have h6 : Real.sqrt (x + 1 / 2 + Real.sqrt (4 * x + 1) / 2) = Real.sqrt (((Real.sqrt (4 * x + 1) + 1) / 2) ^ 2) := by
      rw [h5]

    rw [h6]
    rw [Real.sqrt_sq (by linarith [Real.sqrt_nonneg (4 * x + 1), Real.sqrt_nonneg (4 * x + 1)])]

  have h5' : Real.sqrt (x + 1 / 2 - Real.sqrt (4 * x + 1) / 2) = (Real.sqrt (4 * x + 1) - 1) / 2 := by
    have h7 : (Real.sqrt (4 * x + 1) - 1) / 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (show (4 * x + 1 : ℝ) ≥ 0 by linarith), hx]

    have h8 : ((Real.sqrt (4 * x + 1) - 1) / 2) ^ 2 = x + 1 / 2 - Real.sqrt (4 * x + 1) / 2 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (show (4 * x + 1 : ℝ) ≥ 0 by linarith)]

    have h5'' : Real.sqrt (x + 1 / 2 - Real.sqrt (4 * x + 1) / 2) = Real.sqrt (((Real.sqrt (4 * x + 1) - 1) / 2) ^ 2) := by
      rw [h8]

    rw [h5'']
    rw [Real.sqrt_sq (show (0 : ℝ) ≤ (Real.sqrt (4 * x + 1) - 1) / 2 by
        nlinarith [Real.sqrt_nonneg (4 * x + 1), Real.sq_sqrt (show (4 * x + 1 : ℝ) ≥ 0 by linarith), hx]
    )]

  rw [h4, h5']
  nlinarith