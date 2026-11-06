import Mathlib

theorem algebra_187522 : Real.sqrt (5 + Real.sqrt 24) - Real.sqrt (5 - Real.sqrt 24) = Real.sqrt 8 := by
  have h1 : Real.sqrt 24 = 2 * Real.sqrt 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h2 : Real.sqrt (5 + Real.sqrt 24) = Real.sqrt 2 + Real.sqrt 3 := by
    rw [h1]
    have h3 : Real.sqrt (5 + 2 * Real.sqrt 6) = Real.sqrt 2 + Real.sqrt 3 := by
      have h4 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * Real.sqrt 6 := by
        calc
          (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 2) ^ 2 + (Real.sqrt 3) ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring
          _ = (2 + (3 : ℝ) + 2 * (Real.sqrt 2 * Real.sqrt 3)) := by
            have h5 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
            have h6 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
            rw [h5, h6]
            <;> linarith
          _ = (5 + (2 * (Real.sqrt 2 * Real.sqrt 3) : ℝ)) := by ring_nf
          _ = 5 + 2 * Real.sqrt 6 := by
            have h7 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
              rw [← Real.sqrt_mul (by norm_num)]
              all_goals norm_num
            rw [h7]
            <;> ring_nf
            <;> norm_num
      rw [← h4]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      <;> ring_nf
      <;> norm_num
    exact h3
  have h3 : Real.sqrt (5 - Real.sqrt 24) = Real.sqrt 3 - Real.sqrt 2 := by
    rw [h1]
    have h4 : Real.sqrt (5 - 2 * Real.sqrt 6) = Real.sqrt 3 - Real.sqrt 2 := by
      have h5 : (Real.sqrt 3 - Real.sqrt 2) ^ 2 = (5 - 2 * Real.sqrt 6 : ℝ) := by
        calc
          (Real.sqrt 3 - Real.sqrt 2) ^ 2
            = (Real.sqrt 3) ^ 2 + (Real.sqrt 2) ^ 2 - 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
          _ = (3 + (2 : ℝ) - 2 * (Real.sqrt 3 * Real.sqrt 2)) := by
            have h6 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
            have h7 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
            rw [h6, h7]
            <;> linarith
            <;> ring_nf <;> norm_num
          _ = (5 - (2 * (Real.sqrt 3 * Real.sqrt 2) : ℝ)) := by ring_nf
          _ = (5 - (2 * (Real.sqrt 3 * Real.sqrt 2) : ℝ)) := by ring_nf
          _ = 5 - 2 * Real.sqrt 6 := by
            have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
              rw [← Real.sqrt_mul (by norm_num)]
              all_goals norm_num
            rw [h8]
            <;> ring_nf
            <;> norm_num
      have h6 : 0 ≤ Real.sqrt 3 - Real.sqrt 2 := by
        have h7 : Real.sqrt 3 ≥ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
        have h8 : Real.sqrt 3 ≥ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
        have h9 : Real.sqrt 2 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
          all_goals norm_num
          all_goals norm_num
        have h10 : Real.sqrt 3 - Real.sqrt 2 ≥ 0 := by linarith
        exact h10
      rw [← h5]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_nonneg, h6]
      <;> ring_nf
      <;> norm_num
    exact h4
  rw [h2, h3]
  have h6 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h7 : Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) - (Real.sqrt (3 : ℝ) - Real.sqrt (2 : ℝ)) = 2 * Real.sqrt 2 := by
    ring_nf
    <;> norm_num
  rw [h7]
  rw [h6]
  <;> ring_nf <;> norm_num