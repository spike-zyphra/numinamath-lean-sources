import Mathlib

open Real

theorem algebra_9440 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x * sin (2 * π / 5) + y * cos (2 * π / 5) = tan (11 * π / 15) * (x * cos (2 * π / 5) - y * sin (2 * π / 5))) :
    y / x = √3 := by

  have h1 : tan (11 * π / 15) = sin (11 * π / 15) / cos (11 * π / 15) := by 
    rw [tan_eq_sin_div_cos]

  rw [h1] at h

  have h2 : cos (11 * π / 15) < 0 := by
    have hpi : 0 < π := Real.pi_pos
    have h3 : π / 2 < 11 * π / 15 := by
      nlinarith [Real.pi_pos, Real.pi_gt_31415]
    have h4 : 11 * π / 15 < π := by
      nlinarith [Real.pi_pos, Real.pi_gt_31415]
    apply cos_neg_of_pi_div_two_lt_of_lt
    all_goals linarith [Real.pi_pos, Real.pi_gt_31415]

  have hcos1 : cos (11 * π / 15) ≠ 0 := by
    intro h0
    nlinarith [h2, h0]

  have h3 : (x * sin (2 * π / 5) + y * cos (2 * π / 5)) * cos (11 * π / 15) = sin (11 * π / 15) * (x * cos (2 * π / 5) - y * sin (2 * π / 5)) := by
    field_simp [hcos1] at h ⊢
    linarith

  have h41 : sin (11 * π / 15) = sin (4 * π / 15) := by
    have h11 : 11 * π / 15 = π - (4 * π / 15) := by
      ring
    rw [h11]
    rw [sin_pi_sub]

  have h42 : cos (11 * π / 15) = -cos (4 * π / 15) := by
    have h11 : 11 * π / 15 = π - (4 * π / 15) := by
      ring
    rw [h11]
    rw [cos_pi_sub]

  rw [h41, h42] at h3

  have h51 : (2 * π / 5 : ℝ) = 6 * π / 15 := by 
    ring

  rw [h51] at h3

  have h61 : sin (4 * π / 15) = sin (2 * π / 3) * cos (6 * π / 15) - cos (2 * π / 3) * sin (6 * π / 15) := by
    have h7 : 4 * π / 15 = (2 * π / 3) - (6 * π / 15) := by
      linarith [Real.pi_pos]
    rw [h7]
    rw [sin_sub]

  have h62 : cos (4 * π / 15) = cos (2 * π / 3) * cos (6 * π / 15) + sin (2 * π / 3) * sin (6 * π / 15) := by
    have h7 : 4 * π / 15 = (2 * π / 3) - (6 * π / 15) := by
      linarith [Real.pi_pos]
    rw [h7]
    rw [cos_sub]

  rw [h61, h62] at h3

  have h71 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring]
    rw [sin_pi_sub]
    have hsin : sin (π / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    linarith

  have h72 : cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring]
    rw [cos_pi_sub]
    have hcos : cos (π / 3) = 1 / 2 := by
      exact cos_pi_div_three
    linarith

  rw [h71, h72] at h3

  field_simp [hx] at *
  nlinarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < 6 * π / 15 by linarith [Real.pi_pos] ) (show 6 * π / 15 < Real.pi by linarith [Real.pi_pos] ), Real.sin_sq_add_cos_sq (6 * π / 15), Real.sin_sq_add_cos_sq (4 * π / 15), Real.sin_pos_of_pos_of_lt_pi (show 0 < 4 * π / 15 by linarith [Real.pi_pos] ) (show 4 * π / 15 < Real.pi by linarith [Real.pi_pos] ), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]