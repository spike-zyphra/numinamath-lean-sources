import Mathlib

theorem algebra_12788 : √32/(√16 - √2) = (8 * √2 + 4)/7 ∧ 8 + 2 + 4 + 7 = 21 := by
  constructor
  · -- Prove the equality of the rationalized form
    have h1 : √32 = 4 * √2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h2 : √16 = (4 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    have h3 : (4 - √2 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    field_simp [(show (4 - √2 : ℝ) ≠ 0 by assumption)]
    have h4 : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h4]
  · -- Prove the sum is 21
    norm_num