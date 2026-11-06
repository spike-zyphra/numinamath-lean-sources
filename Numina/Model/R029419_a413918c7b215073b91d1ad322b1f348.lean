import Mathlib

open Real
open scoped Real

theorem inequalities_597505 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  tan (A / 2) * tan (B / 2) * tan (C / 2) *
  (tan (A / 2) + tan (B / 2) + tan (C / 2)) ≤ 1 / 3 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : A / 2 > 0 := by linarith
  have h2 : A / 2 < π / 2 := by
    linarith [hA2]
  have h3 : B / 2 > 0 := by linarith
  have h4 : B / 2 < π / 2 := by
    linarith [hB2]
  have h5 : C / 2 > 0 := by linarith
  have h6 : C / 2 < π / 2 := by
    linarith [hC2]
  have h7 : A / 2 + B / 2 + C / 2 = π / 2 := by
    linarith [hABC]
  have h8 : tan (A / 2) > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals
      linarith
  have h9 : tan (B / 2) > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals
      linarith
  have h10 : tan (C / 2) > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals
      linarith
  have h37 : tan (A / 2) * tan (B / 2) + tan (B / 2) * tan (C / 2) + tan (C / 2) * tan (A / 2) = 1 := by
    have h11 : (tan (A / 2) + tan (B / 2)) / (1 - tan (A / 2) * tan (B / 2)) = 1 / tan (C / 2) := by
      have h14 : tan (A / 2 + B / 2) = Real.tan (π / 2 - C / 2) := by
        have h15 : A / 2 + B / 2 = π / 2 - C / 2 := by
          linarith [h7]
        rw [h15]
      have h15 : tan (A / 2 + B / 2) = (tan (A / 2) + tan (B / 2)) / (1 - tan (A / 2) * tan (B / 2)) := by
        rw [tan_eq_sin_div_cos]
        have h11 : sin (A / 2 + B / 2) = (sin (A / 2) * cos (B / 2) + cos (A / 2) * sin (B / 2)) := by
          rw [sin_add]
        have h12 : cos (A / 2 + B / 2) = (cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2)) := by
          rw [cos_add]
        rw [h11, h12]
        have h13 : cos (A / 2) ≠ 0 := by
          apply ne_of_gt
          apply cos_pos_of_mem_Ioo
          constructor
          · linarith
          · linarith
        have h14 : cos (B / 2) ≠ 0 := by
          apply ne_of_gt
          apply cos_pos_of_mem_Ioo
          constructor
          · linarith
          · linarith
        field_simp [tan_eq_sin_div_cos]
        all_goals
          ring_nf
      have h15' : tan (π / 2 - C / 2) = 1 / tan (C / 2) := by
        have h16 : tan (π / 2 - C / 2) = Real.sin (π / 2 - C / 2) / Real.cos (π / 2 - C / 2) := by
          rw [tan_eq_sin_div_cos]
        rw [h16]
        have h17 : Real.sin (π / 2 - C / 2) = Real.cos (C / 2) := by
          rw [Real.sin_pi_div_two_sub]
        have h18 : Real.cos (π / 2 - C / 2) = Real.sin (C / 2) := by
          rw [Real.cos_pi_div_two_sub]
        rw [h17, h18]
        have h19 : tan (C / 2) = Real.sin (C / 2) / Real.cos (C / 2) := by
          rw [tan_eq_sin_div_cos]
        have h20 : Real.cos (C / 2) ≠ 0 := by
          apply ne_of_gt
          apply cos_pos_of_mem_Ioo
          constructor
          · linarith
          · linarith
        field_simp [h19, h20]
      rw [h15', h15] at h14
      exact h14
    have h14 : tan (C / 2) ≠ 0 := by
      apply ne_of_gt
      apply tan_pos_of_pos_of_lt_pi_div_two
      all_goals
        linarith
    have h15 : 1 - tan (A / 2) * tan (B / 2) ≠ 0 := by
      by_contra h
      have h16 : (tan (A / 2) + tan (B / 2)) / (1 - tan (A / 2) * tan (B / 2)) = 0 := by
        rw [show 1 - tan (A / 2) * tan (B / 2) = 0 by nlinarith]
        norm_num
      have h17 : 1 / tan (C / 2) = 0 := by
        linarith [h11, h16]
      have h18 : tan (C / 2) > 0 := by
        apply tan_pos_of_pos_of_lt_pi_div_two
        all_goals
          linarith
      have h19 : tan (C / 2) = 0 := by
        field_simp at h17 ⊢
        all_goals nlinarith
      linarith
    have h18 : tan (A / 2) * tan (C / 2) + tan (B / 2) * tan (C / 2) = 1 - tan (A / 2) * tan (B / 2) := by
      have h19 : tan (C / 2) ≠ 0 := h14
      field_simp at h11 ⊢
      nlinarith
    linarith
  nlinarith [sq_nonneg (tan (A / 2) * tan (B / 2) - tan (A / 2) * tan (C / 2)), sq_nonneg (tan (B / 2) * tan (C / 2) - tan (A / 2) * tan (B / 2)), sq_nonneg (tan (A / 2) * tan (C / 2) - tan (B / 2) * tan (C / 2)), sq_nonneg (tan (A / 2) - tan (B / 2)), sq_nonneg (tan (A / 2) - tan (C / 2)), sq_nonneg (tan (B / 2) - tan (C / 2)), mul_pos h8 h9, mul_pos h9 h10, mul_pos h8 h10, sq_nonneg (tan (A / 2) * tan (B / 2) + tan (B / 2) * tan (C / 2) + tan (C / 2) * tan (A / 2) - 1) ]