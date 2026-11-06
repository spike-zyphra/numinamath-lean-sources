import Mathlib

theorem algebra_20540 : 8 / (3 * Real.sqrt 3 + 7 * Real.sqrt 27) = Real.sqrt 3 / 9 := by
  have h1 : Real.sqrt 27 = 3 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : 3 * Real.sqrt 3 + 7 * Real.sqrt 27 = 24 * Real.sqrt 3 := by 
    rw [h1]
    ring_nf
  have h3 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  rw [h2]
  have h4 : Real.sqrt 3 > 0 := h3
  field_simp [(show 24 * Real.sqrt 3 ≠ 0 by
    by_contra h
    have h5 : Real.sqrt 3 = 0 := by
      nlinarith [h]
    linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), h5]
  )]
  <;> 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]