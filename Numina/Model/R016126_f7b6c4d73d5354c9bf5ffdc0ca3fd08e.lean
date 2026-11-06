import Mathlib

theorem algebra_187064 : Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15) = Real.sqrt 6 := by
  have h1 : Real.sqrt (4 + Real.sqrt 15) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : Real.sqrt (4 - Real.sqrt 15) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h3 : Real.sqrt (4 + Real.sqrt 15) ≥ Real.sqrt (4 - Real.sqrt 15) := by
    apply Real.sqrt_le_sqrt
    have h4 : (4 + Real.sqrt 15) ≥ (4 - Real.sqrt 15) := by
      linarith [show Real.sqrt 15 ≥ 0 by positivity]
    linarith
  have h4 : (Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15)) ^ 2 = 6 := by
    have h5 : (Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15)) ^ 2 =
      (Real.sqrt (4 + Real.sqrt 15)) ^ 2 + (Real.sqrt (4 - Real.sqrt 15)) ^ 2 - 2 * (Real.sqrt (4 + Real.sqrt 15) * Real.sqrt (4 - Real.sqrt 15)) := by
      ring
    rw [h5]
    have h6 : (Real.sqrt (4 + Real.sqrt 15)) ^ 2 = 4 + Real.sqrt 15 := Real.sq_sqrt (show 4 + Real.sqrt 15 ≥ 0 by positivity)
    have h7 : (Real.sqrt (4 - Real.sqrt 15)) ^ 2 = 4 - Real.sqrt 15 := by
      apply Real.sq_sqrt
      have h15 : Real.sqrt 15 ≤ 4 := by
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num), sq_nonneg (Real.sqrt 15 - 4)]
      linarith
    have h8 : Real.sqrt (4 + Real.sqrt 15) * Real.sqrt (4 - Real.sqrt 15) = 1 := by
      calc
        Real.sqrt (4 + Real.sqrt 15) * Real.sqrt (4 - Real.sqrt 15) = Real.sqrt ((4 + Real.sqrt 15) * (4 - Real.sqrt 15)) := by
          rw [← Real.sqrt_mul (by
            have h15 : Real.sqrt 15 ≥ 0 := Real.sqrt_nonneg 15
            linarith
          )]
        _ = Real.sqrt ((4 + Real.sqrt 15) * (4 - Real.sqrt 15)) := by
          rfl
        _ = Real.sqrt (1 : ℝ) := by
          have hprod : (4 + Real.sqrt 15) * (4 - Real.sqrt 15) = 1 := by
            nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)]
          rw [hprod]
        _ = (1 : ℝ) := by
          rw [Real.sqrt_one]
    rw [h6, h7, h8]
    norm_num
  have h9 : Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15) ≥ 0 := by linarith [Real.sqrt_nonneg (4 + Real.sqrt 15), Real.sqrt_nonneg (4 - Real.sqrt 15), h3]
  have h10 : Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15) = Real.sqrt 6 := by
    have h11 : (Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15)) ^ 2 = 6 := h4
    have h12 : Real.sqrt ((Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15)) ^ 2) = Real.sqrt 6 := by
      rw [h11]
    have h13 : Real.sqrt ((Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15)) ^ 2) = Real.sqrt (4 + Real.sqrt 15) - Real.sqrt (4 - Real.sqrt 15) := by
      rw [Real.sqrt_sq]
      linarith
    nlinarith
  exact h10