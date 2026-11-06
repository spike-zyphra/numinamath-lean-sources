import Mathlib

open Real Set
open scoped Real

theorem algebra_262391 (x : ℝ) (hx : x ∈ Ioo (-1/2) 0) :
    cos ((x + 1) * π) < sin (cos (x * π)) ∧ sin (cos (x * π)) < cos (sin (x * π)) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : -1 / 2 < x := hx1
  have h2 : x < 0 := hx2
  have h3 : -π / 2 < x * π := by 
    nlinarith [Real.pi_pos]
  have h4 : x * π < 0 := by 
    nlinarith [Real.pi_pos]
  have h5 : 0 < cos (x * π) := by 
    have h6 : cos (x * π) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor
      · -- Show -π/2 < x * π
        linarith [h3]
      · -- Show x * π < π/2
        linarith [h4, Real.pi_pos]
    linarith
  have h6 : sin (cos (x * π)) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · -- Show 0 < cos (x * π)
      linarith [h5]
    · -- Show cos (x * π) < π
      nlinarith [Real.pi_pos, Real.sin_sq_add_cos_sq (x * π), Real.pi_gt_three, sq_nonneg (cos (x * π) - 1), sq_nonneg (sin (x * π) - 0), sq_nonneg (x * π), Real.sin_sq_add_cos_sq (x * π)]
  have h7 : sin (cos (x * π)) < cos (sin (x * π)) := by
    have h8 : cos (sin (x * π)) = sin (sin (x * π) + π / 2) := by 
      rw [show sin (x * π) + π / 2 = sin (x * π) + π / 2 by ring]
      rw [Real.sin_add_pi_div_two]
      all_goals linarith
    rw [h8]
    have h10 : -1 < sin (x * π) := by 
      have h11 : sin (x * π) > -1 := by 
        have h14 : sin (x * π) > sin (-π / 2) := by 
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals 
            nlinarith [Real.pi_pos]
        have h15 : sin (-π / 2) = -1 := by 
          rw [show -π / 2 = -(π / 2) by ring]
          rw [sin_neg]
          all_goals 
            norm_num
            all_goals 
              linarith [Real.pi_pos]
        linarith
      linarith
    have h11 : sin (x * π) < 0 := by 
      have h12 : sin (x * π) < sin (0 : ℝ) := by 
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals 
          nlinarith [Real.pi_pos]
      have h13 : sin (0 : ℝ) = 0 := by 
        simp
      linarith [h12, h13]
    have h12 : cos (x * π) < sin (x * π) + π / 2 := by 
      nlinarith [Real.sin_sq_add_cos_sq (x * π), Real.pi_gt_three, Real.pi_pos, sq_nonneg (cos (x * π) - 1), sq_nonneg (sin (x * π) + 1), sq_pos_of_pos (show (0 : ℝ) < cos (x * π) by linarith [h5]), sq_nonneg (sin (x * π)), sq_nonneg (cos (x * π))]
    have h13 : 0 ≤ cos (x * π) := by nlinarith [h5, Real.sin_sq_add_cos_sq (x * π)]
    have h14 : cos (x * π) ≤ π / 2 := by nlinarith [Real.pi_pos, Real.sin_sq_add_cos_sq (x * π), h12, h5, h10, h11, Real.pi_gt_three]
    have h15 : 0 ≤ sin (x * π) + π / 2 := by nlinarith [Real.pi_pos, h10, h11]
    have h17 : sin (cos (x * π)) < sin (sin (x * π) + π / 2) := by 
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals 
        nlinarith [Real.pi_pos, Real.sin_sq_add_cos_sq (x * π), h12, h5, h10, h11, Real.pi_gt_three]
    linarith
  constructor 
  · -- Proof for the first part: \cos((x+1)\pi) < \sin(\cos(x\pi))
    have h6 : cos ((x + 1) * π) < 0 := by 
      have h7 : π / 2 < (x + 1) * π := by 
        nlinarith [Real.pi_pos]
      have h8 : (x + 1) * π < π := by 
        nlinarith [Real.pi_pos]
      have h9 : cos ((x + 1) * π) < 0 := by 
        apply cos_neg_of_pi_div_two_lt_of_lt 
        all_goals 
          nlinarith [Real.pi_pos]
      linarith 
    nlinarith [h6, h6]
  · -- Proof for the second part: \sin(\cos(x\pi)) < \cos(\sin(x\pi))
    linarith [h7]