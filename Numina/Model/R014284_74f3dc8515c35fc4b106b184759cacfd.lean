import Mathlib

theorem algebra_263188 {x : ℝ} (hx : x = (2 + √5) ^ ((1 : ℝ) / 3) - 1 / (2 + √5) ^ ((1 : ℝ) / 3)) :
    x ^ 3 + 3 * x = 4 := by

  set a := (2 + √5 : ℝ) ^ ((1 : ℝ) / 3) with ha
  have ha2 : a ^ 3 = 2 + √5 := by
    have h4 : a ^ 3 = 2 + √5 := by
      have h2 : a = (2 + √5 ) ^ ((1 : ℝ) / 3) := by
        linarith [ha]
      rw [h2]
      have h5 : ((2 + √5 : ℝ) ^ ((1 : ℝ) / 3 )) ^ 3 = (2 + √5 : ℝ) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
      linarith
    linarith

  have hx2 : x = a - 1 / a := by
    rw [hx, ha]
    all_goals ring_nf
  rw [hx2]
  have h1 : a ≠ 0 := by
    by_contra h
    have h2 : a ^ 3 = 2 + √5 := ha2
    rw [h] at h2
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
  have h3 : (a - 1 / a) ^ 3 + 3 * (a - 1 / a) = a ^ 3 - 1 / (a ^ 3) := by
    field_simp [h1]
    <;> nlinarith [sq_nonneg (a + 1 / a), sq_nonneg (a - 1 / a), sq_nonneg (a ^ 2 - 1 / (a ^ 2)), sq_nonneg (a * (1 / a - a)), sq_nonneg ((a ^ 2 - 1) / a), sq_nonneg (a ^ 2), sq_nonneg ((1 / a) ^ 2), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have h4 : a ^ 3 - 1 / (a ^ 3) = 4 := by
    have h5 : a ^ 3 = 2 + √5 := ha2
    have h6 : 1 / (a ^ 3) = (√5 - 2) := by
      rw [h5]
      have h7 : (2 + √5 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ)]
      field_simp [h7]
      <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    rw [h6, h5]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
  linarith [h3, h4]