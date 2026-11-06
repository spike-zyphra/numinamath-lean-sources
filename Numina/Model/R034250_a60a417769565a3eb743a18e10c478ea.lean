import Mathlib

theorem algebra_256807 : Real.sqrt ((2 - Real.sqrt 2) / (2 + Real.sqrt 2)) +
    Real.sqrt ((2 + Real.sqrt 2) / (2 - Real.sqrt 2)) = 2 * Real.sqrt 2 := by

  have h1 : 0 < (2 - Real.sqrt 2) / (2 + Real.sqrt 2) := by
    have h2 : 0 < (2 - Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : 0 < (2 + Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    apply div_pos
    · linarith
    · linarith
  have h4 : 0 < (2 + Real.sqrt 2) / (2 - Real.sqrt 2) := by
    have h5 : 0 < (2 - Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : 0 < (2 + Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    apply div_pos
    · linarith
    · nlinarith
  have h5 : Real.sqrt ((2 - Real.sqrt 2) / (2 + Real.sqrt 2)) = Real.sqrt 2 - 1 := by
    have h6 : ((2 - Real.sqrt 2) / (2 + Real.sqrt 2) : ℝ) = ((Real.sqrt 2 - 1 : ℝ) )^ 2 := by
      have h7 : (2 - Real.sqrt 2 : ℝ) / (2 + Real.sqrt 2) = (3 - 2 * Real.sqrt 2 : ℝ) := by
        field_simp [(show (2 + Real.sqrt 2 : ℝ) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 2)]
      rw [h7]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h6]
    have h7 : Real.sqrt (((Real.sqrt 2 - 1 : ℝ)) ^ 2) = Real.sqrt 2 - 1 := by
      rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt 2 - 1 : ℝ) by
        have h8 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      )]
      all_goals nlinarith
    exact h7
  have h8 : Real.sqrt ((2 + Real.sqrt 2) / (2 - Real.sqrt 2)) = Real.sqrt 2 + 1 := by
    have h9 : ((2 + Real.sqrt 2) / (2 - Real.sqrt 2) : ℝ) = (3 + 2 * Real.sqrt 2 : ℝ) := by
      have h7 : (2 - Real.sqrt 2 : ℝ) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [(show (2 - Real.sqrt 2 : ℝ) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)])]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 2)]
    have h11 : Real.sqrt ((2 + Real.sqrt 2) / (2 - Real.sqrt 2)) = Real.sqrt (3 + 2 * Real.sqrt 2) := by
      rw [h9]
    have h12 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
      have h13 : (3 + 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 1) ^ 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h13]
      have h14 : Real.sqrt ((Real.sqrt 2 + 1) ^ 2) = Real.sqrt 2 + 1 := by
        rw [Real.sqrt_sq (show 0 ≤ Real.sqrt 2 + 1 by positivity)]
        all_goals nlinarith
      exact h14
    rw [h11, h12]
  rw [h5, h8]
  nlinarith