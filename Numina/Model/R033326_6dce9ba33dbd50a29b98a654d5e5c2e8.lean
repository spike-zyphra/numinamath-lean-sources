import Mathlib

theorem algebra_100050 : 2 / (1 / (Real.sqrt 2 + 8 ^ ((1 : ℝ) / 4) + 2) + 1 / (Real.sqrt 2 - 8 ^ ((1 : ℝ) / 4) + 2)) = 4 - Real.sqrt 2 := by

  have h1 : ((8 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 8 := by
    have h2 : ((8 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (8 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals
        norm_num
    have h3 : (8 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 8 := by
      rw [Real.sqrt_eq_rpow]
    rw [h2, h3]

  have h4 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h5 : ((8 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = 2 * Real.sqrt 2 := by
    rw [h1, h4]

  have h104 : Real.sqrt 2 + (8 : ℝ) ^ ((1 : ℝ) / 4) + 2 > 0 := by
    have h7 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    have h8 : (8 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by
      positivity
    positivity

  have h105 : Real.sqrt 2 - (8 : ℝ) ^ ((1 : ℝ) / 4) + 2 > 0 := by
    have h104 : (8 : ℝ) ^ ((1 : ℝ) / 4) < Real.sqrt 2 + 2 := by
      nlinarith [sq_nonneg ((8 : ℝ) ^ ((1 : ℝ) / 4) - (Real.sqrt 2 + 2)), sq_nonneg ((8 : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - (2 * Real.sqrt 2)), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg ((Real.sqrt 2) ^ 2 - (2 * Real.sqrt 2)), Real.sqrt_nonneg 2, Real.sqrt_nonneg 8, h1, h4, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg ((8 : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - 4) ]
    have h7 : Real.sqrt 2 - (8 : ℝ) ^ ((1 : ℝ) / 4) + 2 > 0 := by
      nlinarith
    linarith

  have h8 : (1 / (Real.sqrt 2 + (8 : ℝ) ^ ((1 : ℝ) / 4) + 2) + 1 / (Real.sqrt 2 - (8 : ℝ) ^ ((1 : ℝ) / 4) + 2)) = (2 * Real.sqrt 2 + 4) / (6 + 2 * Real.sqrt 2) := by
    field_simp [h104, h105]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h1, h4, sq_nonneg ((8 : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - (2 * Real.sqrt 2)), Real.sqrt_nonneg 2, Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num) ]
  rw [h8]

  have h102 : (6 + 2 * Real.sqrt 2) ≠ 0 := by
    positivity

  field_simp [h102]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]