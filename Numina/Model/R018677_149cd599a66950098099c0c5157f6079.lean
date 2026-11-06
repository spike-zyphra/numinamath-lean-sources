import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_181030 : tan 1 > arctan 1 := by
  have h1 : arctan 1 = Real.pi / 4 := by
    rw [arctan_one]
  have h3 : tan 1 > 1 := by
    have h1_pos : 0 < (1 : ℝ) := by norm_num
    have h1_lt_pi_div_two : 1 < Real.pi / 2 := by
      linarith [Real.pi_gt_three]
    have h4 : sin 1 > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_gt_three]
    have h5 : cos 1 > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_gt_three]
    have h6 : sin 1 > cos 1 := by
      have h7 : sin 1 > sin (Real.pi / 2 - 1) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
        linarith [Real.pi_gt_three, Real.pi_lt_four]
      have h8 : sin (Real.pi / 2 - 1) = cos 1 := by
        rw [show Real.pi / 2 - 1 = Real.pi / 2 - 1 by rfl]
        rw [sin_pi_div_two_sub]
      linarith [h7, h8]
    have h7 : tan 1 = sin 1 / cos 1 := by
      rw [tan_eq_sin_div_cos]
    have h8 : sin 1 / cos 1 > 1 := by
      have h9 : cos 1 > 0 := h5
      apply (lt_div_iff' (by linarith)).mpr
      linarith [h6, h9]
    linarith [h7, h8]
  have h4 : 1 > arctan 1 := by
    have h1_eq : arctan 1 = Real.pi / 4 := h1
    have h2 : Real.pi / 4 < (1 : ℝ) := by
      linarith [Real.pi_lt_four]
    linarith [h1_eq, h2]
  linarith [h3, h4]