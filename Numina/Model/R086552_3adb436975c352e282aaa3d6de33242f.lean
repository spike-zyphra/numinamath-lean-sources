import Mathlib

open Real

theorem algebra_184853 {c d : ℝ} (hc : c = 2) (hd : d = 1 / 4) :
    sqrt (c - d) / (c^2 * sqrt (2 * c)) * (sqrt ((c - d) / (c + d)) + sqrt ((c^2 + c * d) / (c^2 - c * d))) = 1 / 3 := by
  rw [hc, hd]
  have h1 : sqrt (2 - (1 / 4 : ℝ)) = Real.sqrt 7 / 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : sqrt (2 * (2 : ℝ)) = 2 := by
    rw [Real.sqrt_eq_cases]
    norm_num
  have h3 : sqrt (((2 : ℝ) - (1 / 4 : ℝ)) / ((2 : ℝ) + (1 / 4 : ℝ))) = Real.sqrt 7 / 3 := by
    have h4 : ((2 : ℝ) - (1 / 4 : ℝ)) / ((2 : ℝ) + (1 / 4 : ℝ)) = (7 / 4 : ℝ) / (9 / 4 : ℝ) := by norm_num
    rw [h4]
    have h5 : (7 / 4 : ℝ) / (9 / 4 : ℝ) = (7 / 9 : ℝ) := by
      field_simp
      <;> norm_num
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h6 : sqrt (((2 : ℝ) ^ 2 + (2 : ℝ) * (1 / 4 : ℝ)) / ((2 : ℝ) ^ 2 - (2 : ℝ) * (1 / 4 : ℝ))) = (3 * Real.sqrt 7) / 7 := by
    have h7 : ((2 : ℝ) ^ 2 + (2 : ℝ) * (1 / 4 : ℝ)) / ((2 : ℝ) ^ 2 - (2 : ℝ) * (1 / 4 : ℝ)) = (9 / 7 : ℝ) := by
      norm_num
    rw [h7]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h2, h3, h6]
  field_simp
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num