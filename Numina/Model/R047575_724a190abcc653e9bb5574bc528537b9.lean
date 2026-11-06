import Mathlib

open Real Set

theorem inequalities_115477 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : (x + y) / 2 ≤ sqrt (x * y) + 1) (h2 : (y + z) / 2 ≤ sqrt (y * z) + 4) :
    |sqrt z - sqrt x| ≤ 3 * sqrt 2 := by
  have h1' : (sqrt x - sqrt y) ^ 2 ≤ 2 := by
    have h3 : sqrt (x * y) = sqrt x * sqrt y := by
      rw [Real.sqrt_mul]
      all_goals nlinarith
    nlinarith [h1, sq_nonneg (sqrt x - sqrt y), sq_nonneg (sqrt x * sqrt y - (x + y) / 4), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show 0 ≤ x by linarith), 
      Real.sq_sqrt (show 0 ≤ y by linarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  have h2' : (sqrt y - sqrt z) ^ 2 ≤ 8 := by
    have h4 : sqrt (y * z) = sqrt y * sqrt z := by
      rw [Real.sqrt_mul]
      all_goals nlinarith
    nlinarith [h2, sq_nonneg (sqrt y - sqrt z), sq_nonneg (sqrt y * sqrt z - (y + z) / 4), 
      Real.sqrt_nonneg y, Real.sqrt_nonneg z, Real.sq_sqrt (show 0 ≤ y by linarith), 
      Real.sq_sqrt (show 0 ≤ z by linarith), mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)]
  have h3 : |sqrt z - sqrt x| ≤ |sqrt z - sqrt y| + |sqrt y - sqrt x| := by
    have h4 : sqrt z - sqrt x = (sqrt z - sqrt y) + (sqrt y - sqrt x) := by
      ring
    rw [h4]
    apply abs_add
  have h4 : |sqrt z - sqrt y| ≤ 2 * sqrt 2 := by
    have h5 : (sqrt z - sqrt y) ^ 2 ≤ 8 := by
      have h4 : (sqrt y - sqrt z) ^ 2 ≤ 8 := h2'
      nlinarith
    have h6 : |sqrt z - sqrt y| = Real.sqrt ((sqrt z - sqrt y) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h6]
    have h7 : Real.sqrt ((sqrt z - sqrt y) ^ 2) ≤ Real.sqrt (8 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    nlinarith
  have h5 : |sqrt y - sqrt x| ≤ Real.sqrt 2 := by
    have h6 : (sqrt x - sqrt y) ^ 2 ≤ 2 := h1'
    have h7 : (sqrt y - sqrt x) ^ 2 ≤ 2 := by
      nlinarith
    have h8 : |sqrt y - sqrt x| = Real.sqrt ((sqrt y - sqrt x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h8]
    have h9 : Real.sqrt ((sqrt y - sqrt x) ^ 2) ≤ Real.sqrt (2 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    nlinarith
  have h6 : |sqrt z - sqrt x| ≤ 3 * sqrt 2 := by
    nlinarith [h3, h4, h5]
  exact h6