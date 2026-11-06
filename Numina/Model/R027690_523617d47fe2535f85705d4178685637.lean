import Mathlib

open Real Set

theorem inequalities_603072 : 1 / 3 < sin (π / 9) ∧ sin (π / 9) < 7 / 20 := by
  have h1 : 0 < π / 9 := by linarith [Real.pi_pos]
  have h2 : sin (π / 9) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h31 : sin (π / 9) > 1 / 3 := by
    have h21 : sin (π / 3) = Real.sqrt 3 / 2 := by
      rw [sin_pi_div_three]
    have h22 : sin (π / 3) = 3 * sin (π / 9) - 4 * (sin (π / 9)) ^ 3 := by
      have h12 : sin (3 * (π / 9)) = 3 * sin (π / 9) - 4 * (sin (π / 9)) ^ 3 := by
        rw [Real.sin_three_mul]
      have h13 : 3 * (π / 9) = π / 3 := by
        ring
      rw [h13] at h12
      linarith
    have h24 : Real.sqrt 3 > 46 / 27 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    nlinarith [sq_nonneg (sin (π / 9) - 1 / 3), sq_pos_of_pos (show 0 < sin (π / 9) by linarith [h2]), sq_nonneg (sin (π / 9) ^ 2 - 1 / 9), sq_nonneg (Real.sqrt 3 - 46 / 27), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h20 : sin (π / 9) < 7 / 20 := by
    have h14 : sin (π / 9) < π / 9 := by
      apply sin_lt
      all_goals
        linarith [Real.pi_pos, h1]
    have h15 : π / 9 < 7 / 20 := by
      linarith [Real.pi_lt_31416]
    linarith [h14, h15]
  constructor
  · linarith [h31]
  · linarith [h20]