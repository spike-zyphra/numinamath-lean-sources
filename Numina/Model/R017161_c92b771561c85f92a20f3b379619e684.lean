import Mathlib

open Real Set
open scoped Real

theorem algebra_246604 : sin (7.5 * π / 180) + cos (7.5 * π / 180) =
    (Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2)) / 2 := by
  have h1 : 7.5 * π / 180 = π / 24 := by 
    linarith [Real.pi_pos]
  rw [h1]

  have h2 : sin (π / 24) + cos (π / 24) = Real.sqrt (1 + sin (2 * (π / 24))) := by
    have h3 : (sin (π / 24) + cos (π / 24)) ^ 2 = 1 + sin (2 * (π / 24)) := by 
      have h4 : sin (2 * (π / 24)) = 2 * sin (π / 24) * cos (π / 24) := by 
        rw [sin_two_mul]
      rw [h4]
      nlinarith [Real.sin_sq_add_cos_sq (π / 24), sq_nonneg (sin (π / 24) - cos (π / 24)), sq_nonneg (sin (π / 24) + cos (π / 24))]
    have h5 : sin (π / 24) + cos (π / 24) ≥ 0 := by
      apply add_nonneg
      · apply sin_nonneg_of_nonneg_of_le_pi
        linarith [Real.pi_pos]
        linarith [Real.pi_pos]
      · apply cos_nonneg_of_mem_Icc
        constructor
        all_goals
        linarith [Real.pi_pos]
    have h6 : Real.sqrt ((sin (π / 24) + cos (π / 24)) ^ 2) = sin (π / 24) + cos (π / 24) := by
      rw [Real.sqrt_sq]
      linarith
    have h7 : Real.sqrt ((sin (π / 24) + cos (π / 24)) ^ 2) = Real.sqrt (1 + sin (2 * (π / 24))) := by
      rw [h3]
    linarith [h7, h6]

  have h3 : sin (2 * (π / 24)) = sin (π / 12) := by 
    ring_nf

  have h4 : sin (π / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have h5 : sin (π / 12) = (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2) - (Real.sqrt 2 / 2) * (1 / 2) := by
      have h1 : π / 12 = (π / 4) - (π / 6) := by ring_nf
      rw [h1]
      rw [sin_sub]
      rw [show sin (π / 4) = Real.sqrt 2 / 2 by 
          rw [sin_pi_div_four]
        , show cos (π / 4) = Real.sqrt 2 / 2 by 
          rw [cos_pi_div_four]
        , show sin (π / 6) = 1 / 2 by 
          rw [sin_pi_div_six]
        , show cos (π / 6) = Real.sqrt 3 / 2 by 
          rw [cos_pi_div_six]
      ]
      all_goals ring
    have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      have h1 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by
        rw [Real.sqrt_mul]
        all_goals norm_num
      rw [h1]
      norm_num
    nlinarith [h5, h6, Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h5 : 1 + sin (2 * (π / 24)) = (4 + Real.sqrt 6 - Real.sqrt 2) / 4 := by 
    rw [h3]
    rw [h4]
    linarith

  have h7 : Real.sqrt ((4 + Real.sqrt 6 - Real.sqrt 2) / 4) = Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2) / 2 := by
    have h8 : Real.sqrt ((4 + Real.sqrt 6 - Real.sqrt 2) / 4) = Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2) / Real.sqrt 4 := by 
      field_simp [Real.sqrt_div]
    have h9 : Real.sqrt (4 : ℝ) = 2 := by 
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
    rw [h9] at h8
    rw [h8]

  have h8 : Real.sqrt (1 + sin (2 * (π / 24))) = Real.sqrt ((4 + Real.sqrt 6 - Real.sqrt 2) / 4) := by 
    rw [h5]

  rw [h2]
  rw [h8]
  rw [h7]