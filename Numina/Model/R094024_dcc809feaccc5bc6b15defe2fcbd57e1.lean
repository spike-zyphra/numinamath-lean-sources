import Mathlib

theorem algebra_321682 : (7/3)^999 * Real.sqrt ((3^1998 + 15^1998)/(7^1998 + 35^1998)) = 1 := by 
  have h1 : (3 ^ 1998 + 15 ^ 1998 : ℝ) / (7 ^ 1998 + 35 ^ 1998 : ℝ) = (3 ^ 1998 : ℝ) / (7 ^ 1998 : ℝ) := by
    have h1 : (3 ^ 1998 + (15 : ℝ) ^ 1998) = (3 ^ 1998 : ℝ) * (1 + (5 : ℝ) ^ 1998) := by 
      ring_nf
      <;> norm_num
      <;> ring_nf
    have h2 : (7 ^ 1998 + (35 : ℝ) ^ 1998) = (7 ^ 1998 : ℝ) * (1 + (5 : ℝ) ^ 1998) := by 
      ring_nf
      <;> norm_num
      <;> ring_nf
    rw [h1, h2]
    have h3 : (1 + (5 : ℝ) ^ 1998) ≠ 0 := by
      linarith [show (5 : ℝ) ^ 1998 > 0 by positivity]
    field_simp [h3]
    <;> ring_nf
  have h2 : Real.sqrt ((3 ^ 1998 + 15 ^ 1998 : ℝ) / (7 ^ 1998 + 35 ^ 1998 : ℝ)) = Real.sqrt ((3 ^ 1998 : ℝ) / (7 ^ 1998 : ℝ)) := by 
    rw [h1]
  have h3 : Real.sqrt ((3 ^ 1998 : ℝ) / (7 ^ 1998 : ℝ)) = (3 ^ 999 : ℝ) / (7 ^ 999 : ℝ) := by
    have h4 : (3 ^ 1998 : ℝ) / (7 ^ 1998 : ℝ) = ((3 ^ 999 : ℝ) / (7 ^ 999 : ℝ)) ^ 2 := by
      field_simp
      ring_nf
    rw [h4]
    have h5 : 0 ≤ ((3 ^ 999 : ℝ) / (7 ^ 999 : ℝ)) := by 
      positivity
    rw [Real.sqrt_sq h5]
  rw [h2, h3]
  field_simp
  <;> ring_nf
  <;> norm_num