import Mathlib

open Real

theorem algebra_246414 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (sqrt (a * b / 2) + sqrt 8) / sqrt ((a * b + 16) / 8 + sqrt (a * b)) = 2 := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : sqrt (a * b / 2) = sqrt (a * b) / Real.sqrt 2 := by
    have h2a : sqrt (a * b / 2) = sqrt ((a * b) / (2 : ℝ)) := by ring_nf
    rw [h2a]
    field_simp [Real.sqrt_div]
  have h3 : sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h4 : ((a * b + 16) / 8 + sqrt (a * b)) = (sqrt (a * b) + 4) ^ 2 / (8 : ℝ) := by
    have h4a : sqrt (a * b) ^ 2 = a * b := by 
      rw [Real.sq_sqrt]
      positivity
    nlinarith [h4a]
  have h5 : sqrt ((a * b + 16) / 8 + sqrt (a * b)) = (sqrt (a * b) + 4) / (2 * Real.sqrt 2) := by
    rw [h4]
    have h6 : sqrt (( (sqrt (a * b) + 4 ) ^ 2 / (8 : ℝ) ) ) =
        sqrt ( (sqrt (a * b) + 4 ) ^ 2 ) / Real.sqrt (8 : ℝ) := by
      field_simp [Real.sqrt_div]
    rw [h6]
    have h7 : sqrt ((sqrt (a * b) + 4) ^ 2) = sqrt (a * b) + 4 := by
      rw [Real.sqrt_sq (show 0 ≤ sqrt (a * b) + 4 by positivity)]
    rw [h7]
    have h8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h8]
    <;> field_simp
  have h6 : sqrt (a * b / 2) + sqrt (8 : ℝ) = (sqrt (a * b) + 4) / Real.sqrt 2 := by
    rw [h2, h3]
    field_simp
    <;> ring_nf <;> norm_num
  rw [h6, h5]
  have h7 : sqrt (a * b) + 4 > 0 := by
    have h7a : sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
    nlinarith
  field_simp [show sqrt (a * b) + 4 ≠ 0 by linarith, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  <;> ring_nf <;> norm_num