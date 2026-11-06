import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10513 {a b : ℝ} (ha : 0 < a ∧ a < π / 4) (hb : 0 < b ∧ b < 1) :
    (sin a) ^ (logb b (sin a)) < (sin a) ^ (logb b (cos a)) ∧
    (sin a) ^ (logb b (cos a)) < (cos a) ^ (logb b (cos a)) := by

  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩

  have h1 : sin a < cos a := by 
    have hpi : π > 0 := by linarith [Real.pi_pos]
    have h3 : a < π / 4 := ha2
    have h4 : sin a < sin (π / 4) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [hpi, ha1, ha2]
    have h5 : sin (π / 4) = cos (π / 4) := by
      have h1 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h2 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      linarith [h1, h2]
    have h6 : cos (π / 4) < cos a := by 
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [hpi, ha1, ha2]
    linarith [h4, h5, h6]

  have h2 : logb b (sin a) > logb b (cos a) := by
    have h4 : sin a < cos a := h1
    have h5 : sin a > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos, ha1, ha2]
    have h6 : cos a > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_pos, ha1, ha2]
    have h7 : logb b (sin a) = (log (sin a) ) / (log b) := by
      field_simp [logb]
    have h8 : logb b (cos a) = (log (cos a) ) / (log b) := by
      field_simp [logb]
    have h9 : log (sin a) < log (cos a) := by
      apply Real.log_lt_log
      all_goals nlinarith [Real.sin_sq_add_cos_sq a, sq_pos_of_pos (show sin a > 0 by apply sin_pos_of_pos_of_lt_pi; linarith [Real.pi_pos, ha1, ha2]; linarith [Real.pi_pos, ha1, ha2]), sq_pos_of_pos (show cos a > 0 by apply cos_pos_of_mem_Ioo; constructor; all_goals linarith [Real.pi_pos, ha1, ha2])]
    have h10 : log b < 0 := by
      have h11 : log b < 0 := by
        apply Real.log_neg
        all_goals linarith
      linarith
    rw [h7, h8]
    apply (div_lt_div_right_of_neg (by linarith)).mpr
    linarith

  have h3 : (sin a) ^ (logb b (sin a)) < (sin a) ^ (logb b (cos a)) := by
    have h4 : 0 < sin a := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos, ha1, ha2]
    have h5 : sin a < 1 := by 
      have h1 : sin a < sin (π / 2) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.sin_pi_div_two, Real.pi_pos, ha1, ha2]
      rw [show sin (π / 2) = 1 by rw [sin_pi_div_two]] at h1
      linarith
    have h6 : logb b (sin a) > logb b (cos a) := h2
    have h7 : (sin a : ℝ) ^ (logb b (sin a)) < (sin a : ℝ) ^ (logb b (cos a)) := by
      have h8 : logb b (sin a) > logb b (cos a) := h2
      have h9 : (sin a : ℝ) ^ (logb b (sin a)) < (sin a : ℝ) ^ (logb b (cos a)) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals nlinarith
      linarith
    linarith

  have h8 : (sin a) ^ (logb b (cos a)) < (cos a) ^ (logb b (cos a)) := by
    have h5 : sin a < cos a := h1
    have h6 : sin a > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_pos, ha1, ha2]
    have h7 : cos a > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_pos, ha1, ha2]
    have h4 : logb b (cos a) > 0 := by
      have h10 : cos a < 1 := by 
        have h11 : cos a < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals nlinarith [Real.pi_pos, ha1, ha2]
        have h12 : cos (0 : ℝ) = 1 := Real.cos_zero
        nlinarith [h12, h11]
      have h11 : log (cos a) < 0 := by
        have h13 : log (cos a) < log (1 : ℝ) := by
          apply Real.log_lt_log
          all_goals nlinarith [Real.sin_sq_add_cos_sq a, sq_pos_of_pos (show sin a > 0 by apply sin_pos_of_pos_of_lt_pi; linarith [Real.pi_pos, ha1, ha2]; linarith [Real.pi_pos, ha1, ha2]), sq_pos_of_pos (show cos a > 0 by apply cos_pos_of_mem_Ioo; constructor; all_goals linarith [Real.pi_pos, ha1, ha2])]
        have h14 : log (1 : ℝ) = 0 := Real.log_one
        linarith [h13, h14]
      have h12 : log b < 0 := by
        have h13 : log b < 0 := by
          apply Real.log_neg
          all_goals linarith
        linarith
      have h13 : logb b (cos a) = log (cos a) / log b := by
        field_simp [logb]
      rw [h13]
      apply div_pos_of_neg_of_neg
      all_goals nlinarith
    have h9 : (sin a : ℝ) ^ (logb b (cos a)) < (cos a : ℝ) ^ (logb b (cos a)) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith
    linarith
  exact ⟨h3, h8⟩