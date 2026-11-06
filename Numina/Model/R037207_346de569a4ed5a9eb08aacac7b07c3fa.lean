import Mathlib

open Real

theorem algebra_294479 : sin (18 * π / 180) ^ 2 + cos (63 * π / 180) ^ 2 +
    sqrt 2 * sin (18 * π / 180) * cos (63 * π / 180) = 1 / 2 := by

  have h1 : 63 * π / 180 = (45 * π / 180) + (18 * π / 180) := by
    ring

  have h2 : cos (63 * π / 180) = cos (45 * π / 180 + (18 * π / 180)) := by
    rw [h1]

  have h3 : cos (45 * π / 180 + (18 * π / 180)) =
      cos (45 * π / 180) * cos (18 * π / 180) - sin (45 * π / 180) * sin (18 * π / 180) := by
    rw [cos_add]

  have h4 : cos (45 * π / 180) = Real.sqrt 2 / 2 := by
    have h45 : 45 * π / 180 = π / 4 := by
      ring_nf
    rw [h45]
    rw [cos_pi_div_four]

  have h5 : sin (45 * π / 180) = Real.sqrt 2 / 2 := by
    have h45 : 45 * π / 180 = π / 4 := by
      ring_nf
    rw [h45]
    rw [sin_pi_div_four]

  have hcos63 : cos (63 * π / 180) = Real.sqrt 2 / 2 * (cos (18 * π / 180) - sin (18 * π / 180)) := by
    rw [h2, h3, h4, h5]
    ring

  rw [hcos63]

  have h8 : sin (18 * π / 180) ^ 2 + (Real.sqrt 2 / 2 * (cos (18 * π / 180) - sin (18 * π / 180))) ^ 2 + Real.sqrt 2 * sin (18 * π / 180) * (Real.sqrt 2 / 2 * (cos (18 * π / 180) - sin (18 * π / 180))) = 1 / 2 := by

    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sin_sq_add_cos_sq (18 * π / 180)]

  linarith