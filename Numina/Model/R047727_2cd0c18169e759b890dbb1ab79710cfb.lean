import Mathlib

open Real

theorem algebra_256441 : tan (π / 9) * tan (2 * π / 9) * tan (π / 3) * tan (4 * π / 9) = 3 := by

  have h1 : sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) = Real.sqrt 3 / 8 := by
    have h1 : sin (4 * π / 9) = cos (π / 18) := by
      have h2 : 4 * π / 9 = π / 2 - π / 18 := by
        linarith [Real.pi_pos]
      rw [h2]
      have h3 : sin (π / 2 - π / 18) = cos (π / 18) := by
        rw [sin_pi_div_two_sub]
      exact h3
    have h2 : sin (π / 9) * sin (2 * π / 9) = (cos (π / 9) - 1 / 2) / 2 := by
      have h3 : sin (π / 9) * sin (2 * π / 9) = (cos (π / 9 - 2 * π / 9) - cos (π / 9 + 2 * π / 9)) / 2 := by
        rw [cos_sub, cos_add]
        ring_nf
      have h4 : π / 9 - 2 * π / 9 = -(π / 9) := by ring
      have h5 : π / 9 + 2 * π / 9 = 3 * π / 9 := by ring
      rw [h4, h5] at h3
      have h6 : cos (-(π / 9)) = cos (π / 9) := by
        rw [cos_neg]
      rw [h6] at h3
      have h7 : 3 * π / 9 = π / 3 := by ring
      rw [h7] at h3
      have h8 : cos (π / 3) = 1 / 2 := by
        exact cos_pi_div_three
      rw [h8] at h3
      linarith
    have h3 : cos (π / 9) = 2 * cos (π / 18) ^ 2 - 1 := by
      have h4 : π / 9 = 2 * (π / 18) := by ring
      rw [h4]
      have h5 : cos (2 * (π / 18)) = 2 * cos (π / 18) ^ 2 - 1 := by
        exact cos_two_mul (π / 18)
      linarith [h5]
    have h4 : sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) =
          ( (cos (π / 9) - 1 / 2) / 2 ) * (cos (π / 18)) := by
      calc
        sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9)
          = (sin (π / 9) * sin (2 * π / 9)) * sin (4 * π / 9) := by ring
        _ = (sin (π / 9) * sin (2 * π / 9)) * (cos (π / 18)) := by
          rw [h1]
        _ = ( (cos (π / 9) - 1 / 2) / 2 ) * (cos (π / 18)) := by
          rw [h2]
    have h5 : cos (3 * (π / 18)) = Real.sqrt 3 / 2 := by
      have h6 : 3 * (π / 18) = π / 6 := by ring
      rw [h6]
      have h7 : cos (π / 6) = Real.sqrt 3 / 2 := by
        exact cos_pi_div_six
      linarith [h7]
    have h7 : 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) = Real.sqrt 3 / 2 := by
      have h8 : 4 * cos (π / 18) ^ 3 - 3 * cos (π / 18) = cos (3 * (π / 18)) := by
        rw [cos_three_mul]
      rw [h8, h5]
    have h8 : ( (cos (π / 9) - 1 / 2) / 2 ) * (cos (π / 18)) = Real.sqrt 3 / 8 := by
      have h9 : cos (π / 9) - 1 / 2 = 2 * cos (π / 18) ^ 2 - 3 / 2 := by
        have h10 : cos (π / 9) = 2 * cos (π / 18) ^ 2 - 1 := h3
        linarith [h10]
      rw [h9]
      nlinarith [h7, sq_nonneg (cos (π / 18) ^ 2 - 1 / 2), sq_nonneg (cos (π / 18) ^ 2 - 3 / 4), sq_nonneg (cos (π / 18) - Real.sqrt 3 / 2), sq_nonneg (cos (π / 18) + Real.sqrt 3 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)) ]
    linarith [h4, h8]

  have h2 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := by
    have h3 : sin (8 * (π / 9)) = 8 * sin (π / 9) * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
      have h4 : sin (8 * (π / 9)) = 2 * sin (4 * (π / 9)) * cos (4 * (π / 9)) := by
        have h5 : 8 * (π / 9) = 2 * (4 * (π / 9)) := by ring
        rw [h5]
        rw [sin_two_mul]
      have h6 : sin (4 * (π / 9)) = 2 * sin (2 * (π / 9)) * cos (2 * (π / 9)) := by
        have h7 : 4 * (π / 9) = 2 * (2 * (π / 9)) := by ring
        rw [h7]
        rw [sin_two_mul]
      have h8 : sin (2 * (π / 9)) = 2 * sin (π / 9) * cos (π / 9) := by
        have h9 : 2 * (π / 9) = 2 * (π / 9) := rfl
        rw [h9]
        rw [sin_two_mul]
      rw [h4, h6, h8]
      all_goals ring_nf
    have h4 : sin (8 * (π / 9)) = sin (π - (π / 9)) := by
      ring_nf
    have h5 : sin (π - (π / 9)) = sin (π / 9) := by
      rw [sin_pi_sub]
    rw [h4, h5] at h3
    have h6 : sin (π / 9) ≠ 0 := by
      apply ne_of_gt
      apply sin_pos_of_pos_of_lt_pi
      all_goals
        linarith [Real.pi_pos]
    have h7 : 1 = 8 * cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) := by
      apply (mul_left_inj' h6).mp
      linarith
    nlinarith

  have htan1 : tan (π / 9) = sin (π / 9) / cos (π / 9) := by
    rw [tan_eq_sin_div_cos]
  have htan2 : tan (2 * π / 9) = sin (2 * π / 9) / cos (2 * π / 9) := by
    rw [tan_eq_sin_div_cos]
  have htan3 : tan (π / 3) = sin (π / 3) / cos (π / 3) := by
    rw [tan_eq_sin_div_cos]
  have htan4 : tan (4 * π / 9) = sin (4 * π / 9) / cos (4 * π / 9) := by
    rw [tan_eq_sin_div_cos]
  rw [htan1, htan2, htan3, htan4]

  have h3 : sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h4 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three

  have h7 : sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) = Real.sqrt 3 / 8 := h1
  have h8 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := h2

  have h9 : sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) * sin (π / 3) = 3 / 16 := by
    have h8' : sin (π / 3) = Real.sqrt 3 / 2 := h3
    have h9' : sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) = Real.sqrt 3 / 8 := h1
    calc
      sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9) * sin (π / 3)
        = (sin (π / 9) * sin (2 * π / 9) * sin (4 * π / 9)) * sin (π / 3) := by ring
      _ = (Real.sqrt 3 / 8) * (Real.sqrt 3 / 2) := by rw [h9', h8']
      _ = (3 : ℝ) / 16 := by
        have h10 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        nlinarith

  have h10 : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) * cos (π / 3) = 1 / 16 := by
    have h9' : cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) = 1 / 8 := h2
    have h10' : cos (π / 3) = 1 / 2 := h4
    calc
      cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) * cos (π / 3)
        = (cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9)) * cos (π / 3) := by ring
      _ = (1 / 8) * (1 / 2) := by rw [h9', h10']
      _ = (1 : ℝ) / 16 := by
        norm_num

  have h11 : sin (π / 9) * sin (2 * π / 9) * (sin (4 * π / 9) ) * sin (π / 3) / (cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) * cos (π / 3)) = 3 := by
    rw [show sin (π / 9) * sin (2 * π / 9) * (sin (4 * π / 9) ) * sin (π / 3) = 3 / 16 by linarith [h9], show cos (π / 9) * cos (2 * π / 9) * cos (4 * π / 9) * cos (π / 3) = 1 / 16 by linarith [h10]]
    all_goals
      norm_num

  field_simp [show cos (π / 9) ≠ 0 by
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos], show cos (2 * π / 9) ≠ 0 by
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos], show cos (4 * π / 9) ≠ 0 by
    apply ne_of_gt
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos], show cos (π / 3) ≠ 0 by
    rw [h4]
    norm_num
  ] at h11 ⊢
  all_goals
    linarith [h11]