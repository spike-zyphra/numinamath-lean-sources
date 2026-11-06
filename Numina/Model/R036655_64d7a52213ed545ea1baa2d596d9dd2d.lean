import Mathlib

open Real Set
open scoped Real

theorem calculus_17183 :
  IsLeast {x | 0 < x ∧ tan (2 * x) + tan (3 * x) = 1 / cos (3 * x)} (π / 14) := by
  constructor
  · -- Show that π/14 is in the set
    constructor
    · -- Show that 0 < π/14
      linarith [Real.pi_pos]
    · -- Show that tan(2*(π/14)) + tan(3*(π/14)) = 1/cos(3*(π/14))
      have h1 : 2 * (π / 14) = π / 7 := by ring
      have h2 : 3 * (π / 14) = 3 * π / 14 := by ring
      rw [h1, h2]
      have eq1 : tan (π / 7) + tan (3 * π / 14) = 1 / cos (3 * π / 14) := by
        have h3 : tan (π / 7) = sin (π / 7) / cos (π / 7) := by rw [tan_eq_sin_div_cos]
        have h4 : tan (3 * π / 14) = sin (3 * π / 14) / cos (3 * π / 14) := by rw [tan_eq_sin_div_cos]
        rw [h3, h4]
        have h5 : sin (π / 7) * cos (3 * π / 14) + cos (π / 7) * sin (3 * π / 14) = cos (π / 7) := by
          have h6 : sin (π / 7) * cos (3 * π / 14) + cos (π / 7) * sin (3 * π / 14) = sin (π / 7 + 3 * π / 14) := by
            rw [sin_add]
            all_goals ring
          rw [h6]
          have h7 : π / 7 + 3 * π / 14 = 5 * π / 14 := by ring
          rw [h7]
          have h8 : sin (5 * π / 14) = cos (π / 7) := by
            have h9 : 5 * π / 14 = π / 2 - π / 7 := by
              linarith [Real.pi_pos]
            rw [h9]
            rw [sin_pi_div_two_sub]
          linarith [h8]
        have h8 : cos (π / 7) ≠ 0 := by
          apply ne_of_gt
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · linarith [Real.pi_pos]
          · linarith [Real.pi_pos]
        have h9 : cos (3 * π / 14) ≠ 0 := by
          apply ne_of_gt
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · linarith [Real.pi_pos]
          · linarith [Real.pi_pos]
        field_simp [h8, h9]
        nlinarith [h5, Real.sin_sq_add_cos_sq (π / 7), Real.sin_sq_add_cos_sq (3 * π / 14)]
      linarith [eq1]
  · -- Show that π/14 is the smallest element in the set
    intro x hx
    rcases hx with ⟨hx_pos, heq⟩
    by_contra h
    push_neg at h
    have h1 : 0 < x := by linarith
    have h2 : x < π / 14 := by linarith
    have h3 : 0 < 2 * x := by linarith
    have h4 : 2 * x < π / 7 := by
      linarith [h2]
    have h5 : 0 < 3 * x := by linarith
    have h6 : 3 * x < 3 * π / 14 := by
      linarith [h2]
    have eq1 : tan (2 * x) + tan (3 * x) = 1 / cos (3 * x) := heq
    have eq2 : sin (5 * x) = cos (2 * x) := by
      have h7 : cos (2 * x) ≠ 0 := by
        apply ne_of_gt
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos, h3, h4]
        · linarith [Real.pi_pos, h3, h4]
      have h8 : cos (3 * x) ≠ 0 := by
        apply ne_of_gt
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos, h5, h6]
        · linarith [Real.pi_pos, h5, h6]
      have h9 : tan (2 * x) = sin (2 * x) / cos (2 * x) := by rw [tan_eq_sin_div_cos]
      have h10 : tan (3 * x) = sin (3 * x) / cos (3 * x) := by rw [tan_eq_sin_div_cos]
      rw [h9, h10] at eq1
      have h77 : cos (2 * x) ≠ 0 := h7
      have h88 : cos (3 * x) ≠ 0 := h8
      field_simp [h7, h8] at eq1 ⊢
      have h11 : sin (2 * x) * cos (3 * x) + cos (2 * x) * sin (3 * x) = cos (2 * x) := by
        nlinarith [Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq (3 * x)]
      have h12 : sin (2 * x) * cos (3 * x) + cos (2 * x) * sin (3 * x) = sin (5 * x) := by
        have : sin (5 * x) = sin (2 * x + 3 * x) := by ring_nf
        rw [this]
        rw [sin_add]
        all_goals ring
      linarith [h11, h12]
    -- Show contradiction
    have h33 : sin (5 * x) < sin (5 * (π / 14)) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
      nlinarith [Real.pi_pos, h1, h2, h4, Real.pi_gt_three]
    have h22 : sin (5 * (π / 14)) = cos (π / 7) := by
      have h100 : 5 * (π / 14) = π / 2 - π / 7 := by ring
      rw [h100]
      rw [Real.sin_pi_div_two_sub]
    have h11 : cos (2 * x) = sin (5 * x) := by linarith [eq2]
    have h34 : cos (2 * x) < cos (π / 7) := by
      nlinarith [h33, h22, eq2]
    have h10 : 2 * x < π / 7 := h4
    have h11 : cos (2 * x) > cos (π / 7) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
      nlinarith [Real.pi_pos, h3, h10, Real.pi_gt_three]
    linarith [h11, h34]