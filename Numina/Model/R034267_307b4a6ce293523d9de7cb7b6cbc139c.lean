import Mathlib

open Real

theorem algebra_230873 : arcsin (sin (sqrt 3)) - arcsin (cos 5) = (5 * π / 2) - 5 - sqrt 3 := by
  have h1 : arcsin (sin (sqrt 3)) = Real.pi - sqrt 3 := by
    have h1 : Real.pi / 2 ≤ sqrt 3 := by
      nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    have h3 : arcsin (sin (sqrt 3)) = arcsin (sin (Real.pi - sqrt 3)) := by
      have h4 : sin (sqrt 3) = sin (Real.pi - sqrt 3) := by
        rw [sin_pi_sub]
      rw [h4]
    have h4 : -(Real.pi / 2) ≤ Real.pi - sqrt 3 := by
      nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    have h5 : Real.pi - sqrt 3 ≤ Real.pi / 2 := by
      nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    have h6 : arcsin (sin (Real.pi - sqrt 3)) = Real.pi - sqrt 3 := by
      rw [Real.arcsin_sin]
      all_goals linarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
    rw [h3, h6]
  have h2 : arcsin (cos 5) = 5 - 3 * Real.pi / 2 := by
    have h7 : cos 5 = sin (5 + Real.pi / 2) := by
      rw [show 5 + Real.pi / 2 = (5 : ℝ) + Real.pi / 2 by ring]
      rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
      ring
    have h8 : arcsin (cos 5) = arcsin (sin (5 + Real.pi / 2)) := by
      rw [h7]
    rw [h8]
    have h9 : arcsin (sin (5 + Real.pi / 2)) = 5 - 3 * Real.pi / 2 := by
      have h10 : sin (5 + Real.pi / 2) = sin (5 - 3 * Real.pi / 2) := by
        have h11 : 5 + Real.pi / 2 = (5 - 3 * Real.pi / 2) + 2 * Real.pi  := by
          linarith [Real.pi_pos]
        rw [h11]
        have h12 : sin ((5 - 3 * Real.pi / 2) + 2 * Real.pi) = sin (5 - 3 * Real.pi / 2)  := by
          rw [sin_add, sin_two_pi, cos_two_pi]
          ring
        linarith [h12]
      have h11 : -Real.pi / 2 ≤ 5 - 3 * Real.pi / 2  := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      have h12 : 5 - 3 * Real.pi / 2 ≤ Real.pi / 2  := by
        nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
      rw [h10]
      have h13 : arcsin (sin (5 - 3 * Real.pi / 2)) = 5 - 3 * Real.pi / 2  := by
        apply Real.arcsin_sin
        all_goals linarith [Real.pi_gt_31415, Real.pi_lt_31416]
      linarith [h13, h11, h12]
    linarith [h9]
  rw [h1, h2]
  nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]