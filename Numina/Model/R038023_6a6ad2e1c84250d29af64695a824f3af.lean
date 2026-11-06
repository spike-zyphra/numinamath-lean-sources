import Mathlib

open Real Set
open scoped Real

theorem inequalities_113230 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (h : sin A ^ 2 + sin B ^ 2 + sin C ^ 2 = 1) :
    π / 2 ≤ A + B + C ∧ A + B + C ≤ π := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  constructor
  · -- Prove π / 2 ≤ A + B + C
    by_contra h1
    push_neg at h1
    have h11 : sin A > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hA1, hA2, Real.pi_pos]
      linarith [hA1, hA2, Real.pi_pos]
    have h12 : sin B > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hB1, hB2, Real.pi_pos]
      linarith [hB1, hB2, Real.pi_pos]
    have h13 : sin C > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hC1, hC2, Real.pi_pos]
      linarith [hC1, hC2, Real.pi_pos]
    have h2 : A + B + C < π / 2 := by linarith [h1]
    have h3 : A < π / 2 - (B + C) := by linarith [h2]
    have h4 : sin A < cos (B + C) := by
      have h7 : A < π / 2 - (B + C) := h3
      have h8 : sin A < sin (π / 2 - (B + C)) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [hA1, hA2, hB1, hB2, hC1, hC2, h7, Real.pi_pos, h1]
      have h9 : sin (π / 2 - (B + C)) = cos (B + C) := by
        rw [sin_pi_div_two_sub]
      linarith [h8, h9]
    have h41 : cos (B + C) = cos B * cos C - sin B * sin C := by
      rw [cos_add]
    have h8 : sin A ^ 2 < cos (B + C) ^ 2 := by
      nlinarith [h4, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq (B + C)]
    have h9 : cos (B + C) ^ 2 = (cos B * cos C - sin B * sin C) ^ 2 := by
      rw [h41]
    nlinarith [h8, h9, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, h, mul_pos h11 h12, mul_pos h11 h13, mul_pos h12 h13]
  · -- Prove A + B + C ≤ π
    by_contra h2
    push_neg at h2
    have h11 : sin A > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hA1, hA2, Real.pi_pos]
      linarith [hA1, hA2, Real.pi_pos]
    have h12 : sin B > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hB1, hB2, Real.pi_pos]
      linarith [hB1, hB2, Real.pi_pos]
    have h13 : sin C > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hC1, hC2, Real.pi_pos]
      linarith [hC1, hC2, Real.pi_pos]
    have h6 : A > π - (B + C) := by linarith [h2]
    have h7 : B > π - (A + C) := by linarith [h2]
    have h8 : C > π - (A + B) := by linarith [h2]
    have h9 : cos A < - (cos (B + C)) := by
      have h14 : cos A < cos (π - (B + C)) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals nlinarith [hA1, hA2, h6, Real.pi_pos, Real.pi_gt_three]
      have h15 : cos (π - (B + C)) = - cos (B + C) := by
        rw [cos_pi_sub]
      linarith [h14, h15]
    have h10 : cos (B + C) = cos B * cos C - sin B * sin C := by
      rw [cos_add]
    have h31 : cos B < - (cos (A + C)) := by
      have h8 : cos B < cos (π - (A + C)) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals nlinarith [hB1, hB2, h7, Real.pi_pos, Real.pi_gt_three]
      have h15 : cos (π - (A + C)) = - cos (A + C) := by
        rw [cos_pi_sub]
      linarith [h8, h15]
    have h32 : cos (A + C) = cos A * cos C - sin A * sin C := by
      rw [cos_add]
    have h33 : cos C < - (cos (A + B)) := by
      have h8 : cos C < cos (π - (A + B)) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals nlinarith [hC1, hC2, h8, Real.pi_pos, Real.pi_gt_three]
      have h15 : cos (π - (A + B)) = - cos (A + B) := by
        rw [cos_pi_sub]
      linarith [h8, h15]
    have h34 : cos (A + B) = cos A * cos B - sin A * sin B := by
      rw [cos_add]
    have h15 : sin A > 0 := h11
    have h16 : sin B > 0 := h12
    have h17 : sin C > 0 := h13
    have h18 : cos A > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> nlinarith [hA1, hA2, Real.pi_pos, Real.pi_gt_three]
    have h19 : cos B > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> nlinarith [hB1, hB2, Real.pi_pos, Real.pi_gt_three]
    have h20 : cos C > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> nlinarith [hC1, hC2, Real.pi_pos, Real.pi_gt_three]
    nlinarith [h9, h31, h33, h10, h32, h34, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, h, mul_pos h11 h12, mul_pos h12 h13, mul_pos h11 h13, mul_pos h18 h19, mul_pos h19 h20, mul_pos h18 h20]