import Mathlib

open Real Set

theorem calculus_12598 : 1 / cos (80 * π / 180) - sqrt 3 / sin (80 * π / 180) = 4 := by
  have h1 : sin (80 * π / 180) > 0 := by
    have h1 : 0 < 80 * π / 180 := by
      have h2 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : sin (80 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals
        nlinarith [Real.pi_gt_three]
    linarith
  have h2 : cos (80 * π / 180) > 0 := by
    have h1 : 0 < 80 * π / 180 := by
      have h2 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : cos (80 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  have h3 : sin (80 * π / 180) ^ 2 + cos (80 * π / 180) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (80 * π / 180)
  have h4 : sin (80 * π / 180) - Real.sqrt 3 * cos (80 * π / 180) = 2 * sin (20 * π / 180) := by
    have h5 : sin (80 * π / 180) - Real.sqrt 3 * cos (80 * π / 180) = 2 * sin (80 * π / 180 - π / 3) := by
      rw [show 80 * π / 180 - π / 3 = (80 * π / 180) - (π / 3) by ring]
      have h6 : sin ((80 * π / 180) - (π / 3)) = sin (80 * π / 180) * cos (π / 3) - cos (80 * π / 180) * sin (π / 3) := by
        rw [sin_sub]
      rw [h6]
      have h7 : cos (π / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      have h8 : sin (π / 3) = Real.sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      rw [h7, h8]
      ring_nf
    have h6 : 80 * π / 180 - π / 3 = 20 * π / 180 := by
      nlinarith [Real.pi_pos]
    rw [h6] at h5
    linarith
  have h5 : cos (80 * π / 180) * sin (80 * π / 180) = (1 / 2) * sin (160 * π / 180) := by
    have h4 : sin (160 * π / 180) = 2 * sin (80 * π / 180) * cos (80 * π / 180) := by
      have h3 : 160 * π / 180 = 2 * (80 * π / 180) := by
        ring_nf
      rw [h3]
      rw [show sin (2 * (80 * π / 180)) = 2 * sin (80 * π / 180) * cos (80 * π / 180) by
        rw [sin_two_mul]
      ]
    linarith [h4]
  have h3 : sin (160 * π / 180) = sin (20 * π / 180) := by
    have h4 : 160 * π / 180 = Real.pi - (20 * π / 180) := by
      nlinarith [Real.pi_pos]
    rw [h4]
    have h5 : sin (Real.pi - (20 * π / 180)) = sin (20 * π / 180) := by
      rw [sin_pi_sub]
    linarith [h5]
  have h7 : cos (80 * π / 180) * sin (80 * π / 180) = (1 / 2) * sin (20 * π / 180) := by
    rw [h5, h3]
  have h13 : sin (20 * π / 180) > 0 := by
    have h1 : 0 < 20 * π / 180 := by
      have h2 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : sin (20 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals
        nlinarith [Real.pi_gt_three]
    linarith
  have h20 : (1 / cos (80 * π / 180) - Real.sqrt 3 / sin (80 * π / 180)) =
      (sin (80 * π / 180) - Real.sqrt 3 * cos (80 * π / 180)) / (cos (80 * π / 180) * sin (80 * π / 180)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
    all_goals ring
  rw [h20]
  rw [h4, h7]
  have h10 : sin (20 * π / 180) ≠ 0 := by
    linarith [h13]
  field_simp [h10]
  all_goals nlinarith