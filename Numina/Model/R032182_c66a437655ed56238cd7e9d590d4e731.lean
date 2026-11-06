import Mathlib

theorem algebra_320891 {x : ℝ}
    (hx : x = (20 + 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3) + (20 - 14 * Real.sqrt 2) ^ ((1 : ℝ) / 3)) :
    Real.sqrt (2009 * x) = 14 * Real.sqrt 41 := by

  have h1 : (20 + 14 * Real.sqrt 2 : ℝ) = (2 + Real.sqrt 2) ^ 3 := by
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have h2 : (20 - 14 * Real.sqrt 2 : ℝ) = (2 - Real.sqrt 2) ^ 3 := by
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have h3 : (20 + 14 * Real.sqrt 2 : ℝ) ^ ((1 : ℝ) / 3) = (2 + Real.sqrt 2) := by
    have h4 : (20 + 14 * Real.sqrt 2 : ℝ) = (2 + Real.sqrt 2) ^ 3 := h1
    rw [h4]
    have h5 : ((2 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 + Real.sqrt 2) := by
      have h8 : ((2 + Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 + Real.sqrt 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      exact h8
    exact h5

  have h4 : (20 - 14 * Real.sqrt 2 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2) := by
    have h5 : (20 - 14 * Real.sqrt 2 : ℝ) = (2 - Real.sqrt 2) ^ 3 := h2
    rw [h5]
    have h6 : ((2 - Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2) := by
      have h8 : ((2 - Real.sqrt 2) ^ 3 : ℝ) ^ ((1 : ℝ) / 3) = (2 - Real.sqrt 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      exact h8
    exact h6

  have hx' : x = 4 := by
    rw [hx]
    rw [h3, h4]
    nlinarith

  rw [hx']
  have h7 : Real.sqrt (2009 * (4 : ℝ)) = 14 * Real.sqrt 41 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.sq_sqrt]
  exact h7