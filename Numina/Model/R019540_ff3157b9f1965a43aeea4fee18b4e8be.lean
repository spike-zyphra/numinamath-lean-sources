import Mathlib

open Real Set
open scoped Real

theorem algebra_292015 : (sin (7 * π / 180) + sin (8 * π / 180) * cos (15 * π / 180)) /
    (cos (7 * π / 180) - sin (8 * π / 180) * sin (15 * π / 180)) = 2 - sqrt 3 := by

  have h1 : sin (7 * π / 180) = sin (15 * π / 180 - 8 * π / 180) := by
    ring_nf

  have h2 : sin (15 * π / 180 - 8 * π / 180) = sin (15 * π / 180) * cos (8 * π / 180) - cos (15 * π / 180) * sin (8 * π / 180) := by
    rw [sin_sub]

  have h3 : cos (7 * π / 180) = cos (15 * π / 180 - 8 * π / 180) := by
    ring_nf

  have h4 : cos (15 * π / 180 - 8 * π / 180) = cos (15 * π / 180) * cos (8 * π / 180) + sin (15 * π / 180) * sin (8 * π / 180) := by
    rw [cos_sub]

  have h7 : sin (7 * π / 180) = sin (15 * π / 180) * cos (8 * π / 180) - cos (15 * π / 180) * sin (8 * π / 180) := by
    rw [h1, h2]

  have h8 : cos (7 * π / 180) = cos (15 * π / 180) * cos (8 * π / 180) + sin (15 * π / 180) * sin (8 * π / 180) := by
    rw [h3, h4]

  have h9 : sin (7 * π / 180) + sin (8 * π / 180) * cos (15 * π / 180) = sin (15 * π / 180) * cos (8 * π / 180) := by
    rw [h7]
    have h10 : cos (15 * π / 180) * sin (8 * π / 180) - sin (8 * π / 180) * cos (15 * π / 180) = 0 := by
      ring_nf
    nlinarith [h10]

  have h10 : cos (7 * π / 180) - sin (8 * π / 180) * sin (15 * π / 180) = cos (15 * π / 180) * cos (8 * π / 180) := by
    rw [h8]
    have h11 : sin (15 * π / 180) * sin (8 * π / 180) - sin (8 * π / 180) * sin (15 * π / 180) = 0 := by
      ring_nf
    nlinarith [h11]

  have h11 : cos (15 * π / 180) ≠ 0 := by
    have h1 : 0 < 15 * π / 180 := by 
      nlinarith [Real.pi_pos]
    have h2 : 15 * π / 180 < Real.pi / 2 := by
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h3 : cos (15 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos]
      linarith [Real.pi_pos, h1]
    nlinarith

  have h13 : (sin (7 * π / 180) + sin (8 * π / 180) * cos (15 * π / 180)) / (cos (7 * π / 180) - sin (8 * π / 180) * sin (15 * π / 180)) = sin (15 * π / 180) / cos (15 * π / 180) := by
    rw [h9, h10]
    have hcosne : cos (15 * π / 180) ≠ 0 := h11
    have hcosne2 : cos (8 * π / 180) ≠ 0 := by
      have h1 : 0 < 8 * π / 180 := by 
        linarith [Real.pi_pos]
      have h2 : 8 * π / 180 < Real.pi / 2 := by
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h3 : cos (8 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [Real.pi_pos]
        linarith [Real.pi_pos, h1]
      nlinarith
    field_simp [hcosne, hcosne2]
    <;> ring_nf <;> simp [hcosne, hcosne2] <;> nlinarith [Real.sqrt_nonneg 3]

  rw [h13]

  have htan15 : sin (15 * π / 180) / cos (15 * π / 180) = 2 - Real.sqrt 3 := by
    have h1 : sin (15 * π / 180) = sin (Real.pi / 12) := by
      ring_nf
    have h2 : cos (15 * π / 180) = cos (Real.pi / 12) := by
      ring_nf
    rw [h1, h2]
    have h5 : sin (Real.pi / 12) = sin (Real.pi / 4 - Real.pi / 6) := by 
      ring_nf
    have h6 : sin (Real.pi / 4 - Real.pi / 6) = sin (Real.pi / 4) * cos (Real.pi / 6) - cos (Real.pi / 4) * sin (Real.pi / 6) := by
      rw [sin_sub]
    have h7 : cos (Real.pi / 12) = cos (Real.pi / 4 - Real.pi / 6) := by 
      ring_nf
    have h8 : cos (Real.pi / 4 - Real.pi / 6) = cos (Real.pi / 4) * cos (Real.pi / 6) + sin (Real.pi / 4) * sin (Real.pi / 6) := by
      rw [cos_sub]
    rw [h5, h6, h7, h8]
    have h9 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h10 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    have h11 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    have h12 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    rw [h9, h10, h11, h12]
    have h15 : 0 < (2 - Real.sqrt 3 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
    field_simp [(show (Real.sqrt 3 : ℝ) + 1 ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)])]
    <;> ring_nf <;> field_simp <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  linarith [htan15]