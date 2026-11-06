import Mathlib

theorem algebra_325622 {a : ℝ} (ha : a = -2 + Real.sqrt 2) :
    1 + 1 / (2 + 1 / (3 + a)) = Real.sqrt 2 := by
  rw [ha]
  have h1 : (3 + (-2 + Real.sqrt 2 : ℝ) : ℝ) = 1 + Real.sqrt 2 := by
    ring_nf
  have h2 : 1 / (3 + (-2 + Real.sqrt 2 : ℝ) : ℝ) = Real.sqrt 2 - 1 := by
    rw [h1]
    field_simp [(show 1 + Real.sqrt 2 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    )]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> nlinarith
  have h3 : (2 + (1 / (3 + (-2 + Real.sqrt 2 : ℝ)) : ℝ) : ℝ) = 1 + Real.sqrt 2 := by
    rw [h2]
    linarith
  have h4 : 1 / (2 + (1 / (3 + (-2 + Real.sqrt 2 : ℝ)) : ℝ) : ℝ) = Real.sqrt 2 - 1 := by
    rw [h3]
    field_simp [(show 1 + Real.sqrt 2 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    )]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> nlinarith
  rw [h4]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> nlinarith