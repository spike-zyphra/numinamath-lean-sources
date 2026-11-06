import Mathlib

open Real

theorem algebra_269279 : (sqrt 10 + sqrt 14 - sqrt 15 - sqrt 21) / (sqrt 10 + sqrt 14 + sqrt 15 + sqrt 21) = 2 * sqrt 6 - 5 := by
  have h1 : sqrt 10 = sqrt 2 * sqrt 5 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt 14 = sqrt 2 * sqrt 7 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : sqrt 15 = sqrt 3 * sqrt 5 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : sqrt 21 = sqrt 3 * sqrt 7 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h5 : sqrt 6 = sqrt 2 * sqrt 3 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h6 : sqrt 10 + sqrt 14 - sqrt 15 - sqrt 21 = (sqrt 5 + sqrt 7) * (sqrt 2 - sqrt 3) := by
    rw [h1, h2, h3, h4]
    ring_nf
  have h7 : sqrt 10 + sqrt 14 + sqrt 15 + sqrt 21 = (sqrt 5 + sqrt 7) * (sqrt 2 + sqrt 3) := by 
    rw [h1, h2, h3, h4]
    ring_nf
  rw [h6, h7]
  have h8 : sqrt 5 + sqrt 7 > 0 := by
    have h5' : sqrt 5 > 0 := by
      apply sqrt_pos.mpr
      norm_num
    have h7' : sqrt 7 > 0 := by
      apply sqrt_pos.mpr
      norm_num
    linarith
  have h9 : (sqrt 2 - sqrt 3) / (sqrt 2 + sqrt 3) = 2 * sqrt 6 - 5 := by
    have h10 : sqrt 2 + sqrt 3 > 0 := by 
      have h2 : sqrt 2 > 0 := by
        apply sqrt_pos.mpr
        norm_num
      have h3 : sqrt 3 > 0 := by 
        apply sqrt_pos.mpr
        norm_num
      linarith
    field_simp [(show sqrt 2 + sqrt 3 ≠ 0 by linarith)]
    have h11 : sqrt 2 * sqrt 3 = sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
              sq_nonneg (sqrt 2 - sqrt 3), 
              sq_nonneg (sqrt 2), 
              sq_nonneg (sqrt 3), 
              h11
            ]
  have h10 : (sqrt 5 + sqrt 7) * (sqrt 2 - sqrt 3) / ((sqrt 5 + sqrt 7) * (sqrt 2 + sqrt 3)) = (sqrt 2 - sqrt 3) / (sqrt 2 + sqrt 3) := by
    have h8' : sqrt 5 + sqrt 7 > 0 := h8
    have h9' : sqrt 2 + sqrt 3 > 0 := by
      have h2 : sqrt 2 > 0 := by
        apply sqrt_pos.mpr
        norm_num
      have h3 : sqrt 3 > 0 := by 
        apply sqrt_pos.mpr
        norm_num
      linarith
    field_simp [(show sqrt 5 + sqrt 7 ≠ 0 by linarith), 
                (show sqrt 2 + sqrt 3 ≠ 0 by linarith)]
    <;> ring
  rw [h10]
  exact h9