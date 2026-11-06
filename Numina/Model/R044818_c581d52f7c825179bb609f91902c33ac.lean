import Mathlib

open Real

theorem algebra_164464 : sin (20 * π / 180) * cos (50 * π / 180) * sin (60 * π / 180) * cos (10 * π / 180) = 3 / 16 := by
  have h1 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by
    have h2 : 60 * π / 180 = Real.pi / 3 := by
      ring_nf
      <;> field_simp
      <;> ring_nf
      all_goals nlinarith [pi_pos]
    rw [h2]
    exact sin_pi_div_three
  have h5 : cos (50 * π / 180) = sin (40 * π / 180) := by
    have h1 : 50 * π / 180 = Real.pi / 2 - 40 * π / 180 := by
      nlinarith [pi_pos]
    rw [h1]
    rw [cos_pi_div_two_sub]
    all_goals ring_nf
  rw [h1, h5]
  have h3 : sin (20 * π / 180) * sin (40 * π / 180) = (1 / 2) * (cos (20 * π / 180 - 40 * π / 180) - cos (20 * π / 180 + 40 * π / 180)) := by 
    rw [show sin (20 * π / 180) * sin (40 * π / 180) = (1 / 2) * (cos (20 * π / 180 - 40 * π / 180) - cos (20 * π / 180 + 40 * π / 180)) by 
      rw [cos_sub, cos_add]
      ring_nf <;> simp [cos_sq, sin_sq]
      <;> ring_nf
      <;> simp [cos_sq, sin_sq]
      <;> ring_nf
    ]
    all_goals ring_nf
    all_goals simp [cos_sq, sin_sq]
    all_goals ring_nf
    all_goals simp [cos_sq, sin_sq]
    all_goals ring_nf
  have h6 : cos (20 * π / 180 - 40 * π / 180) = cos (20 * π / 180) := by 
    have h7 : 20 * π / 180 - 40 * π / 180 = -(20 * π / 180) := by 
      nlinarith [pi_pos]
    rw [h7]
    rw [cos_neg]
  have h7 : cos (20 * π / 180 + 40 * π / 180) = 1 / 2 := by 
    have h8 : 20 * π / 180 + 40 * π / 180 = Real.pi / 3 := by 
      nlinarith [pi_pos]
    rw [h8]
    exact cos_pi_div_three
  rw [h3, h6, h7]
  have h8 : cos (20 * π / 180) * cos (10 * π / 180) = 1 / 2 * (cos (20 * π / 180 - 10 * π / 180) + cos (20 * π / 180 + 10 * π / 180)) := by
    have hcos_sub : cos (20 * π / 180 - 10 * π / 180) = cos (20 * π / 180) * cos (10 * π / 180) + sin (20 * π / 180) * sin (10 * π / 180) := by
      rw [cos_sub]
    have hcos_add : cos (20 * π / 180 + 10 * π / 180) = cos (20 * π / 180) * cos (10 * π / 180) - sin (20 * π / 180) * sin (10 * π / 180) := by
      rw [cos_add]
    linarith [hcos_sub, hcos_add, Real.cos_sq_add_sin_sq (20 * π / 180), Real.cos_sq_add_sin_sq (10 * π / 180)]
  have h9 : 20 * π / 180 - 10 * π / 180 = 10 * π / 180 := by 
    nlinarith [pi_pos]
  have h10 : 20 * π / 180 + 10 * π / 180 = Real.pi / 6 := by 
    nlinarith [pi_pos]
  have h11 : cos (20 * π / 180 + 10 * π / 180) = Real.sqrt 3 / 2 := by 
    rw [h10]
    exact cos_pi_div_six
  rw [h9, h11] at h8
  nlinarith [pi_pos, sq_nonneg (sin (20 * π / 180) - sin (40 * π / 180)), sq_nonneg (cos (10 * π / 180) - 1 / 2), sq_nonneg (sin (10 * π / 180) - Real.sqrt 3 / 2), Real.sqrt_pos.mpr (by nlinarith : (0 : ℝ) < 3), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), sin_pos_of_pos_of_lt_pi (show 0 < 20 * π / 180 by nlinarith [pi_pos] ), sin_pos_of_pos_of_lt_pi (show 0 < 10 * π / 180 by nlinarith [pi_pos] ), sin_pos_of_pos_of_lt_pi (show 0 < 40 * π / 180 by nlinarith [pi_pos] ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), Real.sqrt_nonneg 3, Real.sin_sq_add_cos_sq (20 * π / 180), Real.sin_sq_add_cos_sq (40 * π / 180), Real.sin_sq_add_cos_sq (10 * π / 180), h8, h1, h5]