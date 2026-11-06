import Mathlib

open Real

theorem algebra_313660 : sqrt (3 + sqrt (5 - sqrt (13 + sqrt 48))) / (sqrt 6 + sqrt 2) = 1 / 2 := by
  have h1 : sqrt 48 = 4 * sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt (13 + sqrt 48) = 1 + 2 * sqrt 3 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
  have h3 : sqrt (5 - sqrt (13 + sqrt 48)) = Real.sqrt 3 - 1 := by
    rw [h2]
    have h4 : (5 - (1 + 2 * Real.sqrt 3 : ℝ)) = (Real.sqrt 3 - 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
    rw [h4]
    have h5 : 0 ≤ Real.sqrt 3 - 1 := by
      have h6 : 1 < (Real.sqrt 3 : ℝ) := by
        rw [Real.lt_sqrt] <;> norm_num
      linarith
    rw [Real.sqrt_sq (h5)]
  have h6 : sqrt (3 + sqrt (5 - sqrt (13 + sqrt 48))) = (Real.sqrt 3 + 1) * (Real.sqrt 2) / 2 := by
    rw [h3]
    have h7 : (3 + (Real.sqrt 3 - 1 : ℝ)) = ((Real.sqrt 3 + 1) / Real.sqrt 2) ^ 2 := by
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    rw [h7]
    have h8 : 0 ≤ (Real.sqrt 3 + 1) / Real.sqrt 2 := by
      have h9 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      apply div_nonneg
      · -- Show that `Real.sqrt 3 + 1 ≥ 0`
        have h10 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
        linarith
      · -- Show that `Real.sqrt 2 > 0`
        linarith
    rw [Real.sqrt_sq (h8)]
    <;> field_simp
    all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  have h7 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h6, h7]
  field_simp
  <;> ring_nf <;> norm_num