import Mathlib

open Real Set
open scoped Real

theorem algebra_225771 {a b : ℚ} (ha : a = 1 / 2) (hb : b = 3 / 16) :
    sin (75 * π / 180) * cos (15 * π / 180) = a + sqrt b := by
  have h1 : sin (75 * π / 180) = cos (15 * π / 180) := by
    have h2 : 75 * π / 180 = π / 2 - (15 * π / 180) := by
      linarith [pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have eq2 : sin (75 * π / 180) * cos (15 * π / 180) = cos (15 * π / 180) ^ 2 := by
    rw [h1]
    <;> ring
  have h3 : cos (15 * π / 180) = (Real.sqrt 2 + Real.sqrt 6) / 4 := by
    have h5 : cos (15 * π / 180) = cos (Real.pi / 12) := by
      ring_nf
    rw [h5]
    have h2 : Real.pi / 12 = (Real.pi / 4) - (Real.pi / 6) := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [cos_sub]
    have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h4 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
      rw [cos_pi_div_six]
    have h5 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h6 : sin (Real.pi / 6) = 1 / 2 := by
      rw [sin_pi_div_six]
    simp only [h3, h4, h5, h6]
    have h7 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    field_simp [h7]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sqrt_nonneg 2, 
        Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (Real.sqrt 2 - Real.sqrt 3)
    ]
  have h3' : cos (15 * π / 180) ^ 2 = (2 + Real.sqrt 3) / 4 := by
    rw [h3]
    have h8 : ((Real.sqrt 2 + Real.sqrt 6) / (4 : ℝ)) ^ 2 = (2 + Real.sqrt 3) / 4 := by
      have h7 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h7]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
          Real.sqrt_nonneg 2, 
          Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        ]
    linarith
  have hA : (a : ℝ) = (1 / 2 : ℝ) := by
    rw [ha]
    all_goals norm_num
  have hB : (b : ℝ) = (3 / 16 : ℝ) := by
    rw [hb]
    all_goals norm_num
  have h5 : sqrt (b : ℝ) = Real.sqrt 3 / 4 := by
    rw [hB]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h6 : (a : ℝ) + sqrt (b : ℝ) = (2 + Real.sqrt 3) / 4 := by
    rw [h5, hA]
    linarith
  rw [eq2]
  all_goals linarith [h3', h6]