import Mathlib

open Real Set
open scoped Real

theorem inequalities_193128 (x : Real) (hx : x ∈ Ioo 0 (π/2)) :
    sin x ≤ cos x ↔ x ≤ π/4 := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Forward direction: If sin x ≤ cos x, prove x ≤ π/4
    intro h3
    by_contra h
    push_neg at h
    have h5 : x > Real.pi / 4 := h
    have h6 : sin x > cos x := by
      have h7 : x > Real.pi / 4 := h5
      have h8 : sin x > Real.sqrt 2 / 2 := by
        have h9 : sin x > sin (Real.pi / 4) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals linarith [Real.pi_pos, hx1, hx2]
        have h10 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [sin_pi_div_four]
        linarith [h9, h10]
      have h10 : cos x < Real.sqrt 2 / 2 := by
        have h11 : cos x < cos (Real.pi / 4) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [Real.pi_pos, hx1, hx2]
        have h12 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [cos_pi_div_four]
        linarith [h11, h12]
      linarith 
    linarith [h3, h6]
  · -- Backward direction: If x ≤ π/4, prove sin x ≤ cos x
    intro h13
    have h4 : cos x > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor
      linarith
      linarith
    have h4' : sin x > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have h16 : sin x ≤ cos x := by
      by_cases h' : x ≤ Real.pi / 4
      · -- If x ≤ π/4, then sin x ≤ cos x 
        have h3 : x ≤ Real.pi / 4 := h'
        have h4 : sin x ≤ sin (Real.pi / 4) := by
          apply Real.sin_le_sin_of_le_of_le_pi_div_two
          all_goals linarith [Real.pi_pos, hx1, hx2]
        have h11 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
          rw [sin_pi_div_four]
        have h8 : cos x ≥ Real.sqrt 2 / 2 := by 
          have h14 : cos x ≥ cos (Real.pi / 4) := by
            apply Real.cos_le_cos_of_nonneg_of_le_pi
            all_goals linarith [Real.pi_pos, hx1, hx2]
          have h15 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
            rw [cos_pi_div_four]
          linarith
        nlinarith [Real.sin_sq_add_cos_sq x, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- If x > π/4, then contradiction 
        have h5 : x > Real.pi / 4 := by 
          linarith 
        have h6 : sin x > cos x := by 
          have h7 : x > Real.pi / 4 := h5
          have h8 : sin x > Real.sqrt 2 / 2 := by 
            have h9 : sin x > sin (Real.pi / 4) := by 
              apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
              all_goals linarith [Real.pi_pos, hx1, hx2]
            have h10 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
              rw [sin_pi_div_four]
            linarith [h9, h10]
          have h10 : cos x < Real.sqrt 2 / 2 := by 
            have h11 : cos x < cos (Real.pi / 4) := by 
              apply Real.cos_lt_cos_of_nonneg_of_le_pi
              all_goals linarith [Real.pi_pos, hx1, hx2]
            have h12 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
              rw [cos_pi_div_four]
            linarith [h11, h12]
          linarith 
        linarith [show sin x ≤ cos x by linarith]
    linarith [h16]