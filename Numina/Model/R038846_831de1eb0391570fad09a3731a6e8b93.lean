import Mathlib

theorem algebra_22562 : Real.sqrt (3 / 4 - Real.sqrt (1 / 2)) - Real.sqrt (3 / 4 + Real.sqrt (1 / 2)) = -1 := by
  have h1 : Real.sqrt (3 / 4 - Real.sqrt (1 / 2)) = (Real.sqrt 2 - 1) / 2 := by
    have h2 : Real.sqrt (3 / 4 - Real.sqrt (1 / 2)) = Real.sqrt ((3 - 2 * Real.sqrt 2) / 4) := by
      have h4 : (3 / 4 - Real.sqrt (1 / 2) : ℝ) = (3 - 2 * Real.sqrt 2) / 4 := by
        have h5 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
        rw [h5]
        linarith
      rw [h4]
    rw [h2]
    have h6 : Real.sqrt ((3 - 2 * Real.sqrt 2) / 4) = (Real.sqrt 2 - 1) / 2 := by
      have h7 : Real.sqrt ((3 - 2 * Real.sqrt 2) / 4) = Real.sqrt (3 - 2 * Real.sqrt 2) / 2 := by
        have h8 : (3 - 2 * Real.sqrt 2 : ℝ) / 4 = (Real.sqrt (3 - 2 * Real.sqrt 2) / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (3 - 2 * Real.sqrt 2), Real.sq_sqrt (show (0 ≤ (3 - 2 * Real.sqrt 2 : ℝ) ) by
            nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          )]
        have h9 : Real.sqrt ((3 - 2 * Real.sqrt 2 : ℝ) / 4) = Real.sqrt ((Real.sqrt (3 - 2 * Real.sqrt 2) / 2) ^ 2) := by
          rw [h8]
        rw [h9]
        have h10 : Real.sqrt ((Real.sqrt (3 - 2 * Real.sqrt 2) / 2) ^ 2) = Real.sqrt (3 - 2 * Real.sqrt 2) / 2 := by
          apply Real.sqrt_sq
          have h6' : Real.sqrt (3 - 2 * Real.sqrt 2) ≥ 0 := by positivity
          nlinarith
          all_goals nlinarith
          all_goals nlinarith
        rw [h10]
      rw [h7]
      have h9 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
        have h9 : (Real.sqrt 2 - 1 : ℝ) ^ 2 = (3 - 2 * Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h10 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt ((Real.sqrt 2 - 1 : ℝ) ^ 2) := by
          rw [h9]
        rw [h10]
        have h11 : Real.sqrt ((Real.sqrt 2 - 1 : ℝ) ^ 2) = Real.sqrt 2 - 1 := by
          have h11 : (Real.sqrt 2 - 1 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt 2 - 1 : ℝ) by linarith [h11] ) ]
        rw [h11]
        all_goals linarith
      rw [h9]
      all_goals linarith
    linarith [h6]
  
  have h2 : Real.sqrt (3 / 4 + Real.sqrt (1 / 2)) = (Real.sqrt 2 + 1) / 2 := by
    have h4 : (3 / 4 + Real.sqrt (1 / 2) : ℝ) = (3 + 2 * Real.sqrt 2) / 4 := by
      have h5 : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h5]
      linarith
    rw [h4]
    have h6 : Real.sqrt ((3 + 2 * Real.sqrt 2) / 4) = (Real.sqrt 2 + 1) / 2 := by
      have h7 : Real.sqrt ((3 + 2 * Real.sqrt 2) / 4) = Real.sqrt (3 + 2 * Real.sqrt 2) / 2 := by
        have h8 : (3 + 2 * Real.sqrt 2 : ℝ) / 4 = (Real.sqrt (3 + 2 * Real.sqrt 2) / 2) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (3 + 2 * Real.sqrt 2), Real.sq_sqrt (show (0 ≤ (3 + 2 * Real.sqrt 2 : ℝ) ) by
            nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          )]
        have h9 : Real.sqrt ((3 + 2 * Real.sqrt 2 : ℝ) / 4) = Real.sqrt ((Real.sqrt (3 + 2 * Real.sqrt 2) / 2) ^ 2) := by
          rw [h8]
        rw [h9]
        have h10 : Real.sqrt ((Real.sqrt (3 + 2 * Real.sqrt 2) / 2) ^ 2) = Real.sqrt (3 + 2 * Real.sqrt 2) / 2 := by
          apply Real.sqrt_sq
          have h6' : Real.sqrt (3 + 2 * Real.sqrt 2) ≥ 0 := by positivity
          nlinarith
          all_goals nlinarith
          all_goals nlinarith
        rw [h10]
      rw [h7]
      have h9 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
        have h9 : (Real.sqrt 2 + 1 : ℝ) ^ 2 = (3 + 2 * Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h10 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt ((Real.sqrt 2 + 1 : ℝ) ^ 2) := by
          rw [h9]
        rw [h10]
        have h11 : Real.sqrt (( (Real.sqrt 2 + 1 : ℝ) ) ^ 2) = Real.sqrt 2 + 1 := by
          have h12 : (Real.sqrt 2 + 1 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          rw [Real.sqrt_sq (show 0 ≤ (Real.sqrt 2 + 1 : ℝ) by linarith [h12] ) ]
        rw [h11]
        all_goals linarith
      rw [h9]
      all_goals linarith
    linarith [h6]

  rw [h1, h2]
  field_simp
  <;> nlinarith
  <;> field_simp
  all_goals nlinarith