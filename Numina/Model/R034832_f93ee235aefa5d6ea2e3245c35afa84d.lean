import Mathlib

open Real

theorem algebra_304683 {F : ℝ → ℝ}
    (hF : F = fun x => 1 / sqrt (x + 2 * sqrt (x - 1)) + 1 / sqrt (x - 2 * sqrt (x - 1))) :
    F (3 / 2) = 4 := by
  have h1 : F (3/2) = 1 / sqrt (3/2 + 2 * sqrt (3/2 - 1)) + 1 / sqrt (3/2 - 2 * sqrt (3/2 - 1)) := by
    rw [hF]
  have h2 : sqrt (3/2 - 1) = Real.sqrt (1/2 : ℝ) := by norm_num
  have h3 : Real.sqrt (1/2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h4 : sqrt (3/2 - 1) = Real.sqrt 2 / 2 := by
    rw [h2, h3]
  have h5 : (3/2 + 2 * sqrt (3/2 - 1)) = (3/2 + Real.sqrt 2) := by
    rw [h4]
    ring_nf
  have h6 : (3/2 - 2 * sqrt (3/2 - 1)) = (3/2 - Real.sqrt 2) := by
    rw [h4]
    ring_nf
  rw [h1, h5, h6]

  have h7 : 0 ≤ (3/2 - Real.sqrt 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]

  have h8 : sqrt ((3/2 + Real.sqrt 2 : ℝ)) = (Real.sqrt 2 + 1) / Real.sqrt 2 := by
    have h12 : ((Real.sqrt 2 + 1) / Real.sqrt 2) ^ 2 = (3/2 + Real.sqrt 2 : ℝ) := by
      have h13 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)
      field_simp
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h10 : 0 ≤ (Real.sqrt 2 + 1) / Real.sqrt 2 := by
      apply div_nonneg
      · -- Show sqrt 2 + 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 2]
      · -- Show sqrt 2 ≥ 0
        positivity
    have h14 : Real.sqrt ((3/2 + Real.sqrt 2 : ℝ)) = (Real.sqrt 2 + 1) / Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> (nlinarith)
    exact h14

  have h9 : sqrt ((3/2 - Real.sqrt 2 : ℝ)) = (Real.sqrt 2 - 1) / Real.sqrt 2 := by
    have h15 : ((Real.sqrt 2 - 1) / Real.sqrt 2) ^ 2 = (3/2 - Real.sqrt 2 : ℝ) := by
      have h13 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)
      field_simp
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h100 : 0 ≤ (Real.sqrt 2 - 1) / Real.sqrt 2 := by
      apply div_nonneg
      · -- Show sqrt 2 - 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      · -- Show sqrt 2 ≥ 0
        positivity
    have h14 : Real.sqrt ((3/2 - Real.sqrt 2 : ℝ)) = (Real.sqrt 2 - 1) / Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> (nlinarith)
    exact h14

  rw [h8, h9]

  have h13 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)
  have h14 : Real.sqrt 2 + 1 > 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h15 : Real.sqrt 2 - 1 > 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]

  field_simp [show Real.sqrt 2 + 1 ≠ 0 by linarith, show Real.sqrt 2 - 1 ≠ 0 by linarith]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]