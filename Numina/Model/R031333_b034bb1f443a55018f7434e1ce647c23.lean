import Mathlib

theorem algebra_117610 : 3 * Real.sqrt (Real.sqrt (7 + Real.sqrt 48)) / (2 * (Real.sqrt 2 + Real.sqrt 6)) = 3 / 4 := by

  -- Compute $\sqrt{48}$
  have h1 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  -- Compute $\sqrt{7 + \sqrt{48}}$
  have h2 : Real.sqrt (7 + Real.sqrt 48) = 2 + Real.sqrt 3 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  -- Compute $\sqrt{\sqrt{7 + \sqrt{48}}}$

  have h3 : Real.sqrt (Real.sqrt (7 + Real.sqrt 48)) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
    rw [h2]
    have h4 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
      have h5 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 3 + 1) / Real.sqrt 2 := by
        have h6 : ((Real.sqrt 3 + 1) / Real.sqrt 2) ^ 2 = 2 + Real.sqrt 3 := by
          field_simp
          <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        have h7 : 0 ≤ (Real.sqrt 3 + 1) / Real.sqrt 2 := by
          apply div_nonneg
          · -- Show Real.sqrt 3 + 1 ≥ 0
            linarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
          · -- Show Real.sqrt 2 > 0
            positivity
        rw [Real.sqrt_eq_iff_sq_eq] at *
        · linarith [h6]
        all_goals nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
      linarith
    linarith

  -- Compute $\sqrt{6}$

  have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h3, h4]
  have h5 : Real.sqrt 2 > 0 := by positivity
  field_simp
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]