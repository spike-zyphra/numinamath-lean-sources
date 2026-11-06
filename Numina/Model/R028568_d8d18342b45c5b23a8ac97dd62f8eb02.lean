import Mathlib

open Real
open scoped Real

theorem inequalities_283275 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  sin A + sin B > sin C ∧ sin B + sin C > sin A ∧ sin A + sin C > sin B := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : C = π - (A + B) := by 
    linarith [hABC]
  have h2 : sin C = sin (A + B) := by
    rw [h1]
    have h3 : sin (π - (A + B)) = sin (A + B) := by 
      rw [sin_pi_sub]
    linarith [h3]
  have h3 : sin A + sin B > sin C := by
    rw [h2]
    have h4 : sin (A + B) = sin A * cos B + cos A * sin B := by
      rw [sin_add]
    rw [h4]
    have h5 : sin A > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h6 : sin B > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h5' : cos A < 1 := by 
      have h7 : A > 0 := hA1
      have h8 : A < π := hA2
      have h9 : cos A < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h6' : cos B < 1 := by 
      have h7 : B > 0 := hB1
      have h8 : B < π := hB2
      have h9 : cos B < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h5'' : 1 - cos B > 0 := by 
      linarith [h6']
    have h6'' : 1 - cos A > 0 := by 
      linarith [h5']
    have h7 : sin A * (1 - cos B) > 0 := by 
      apply mul_pos
      linarith [h5]
      linarith [h6']
    have h8 : sin B * (1 - cos A) > 0 := by 
      apply mul_pos
      linarith [h6]
      linarith [h5']
    nlinarith [h7, h8]
  -- Prove the second inequality: $\sin B + \sin C > \sin A$
  have h4 : sin B + sin C > sin A := by
    have h7 : A = π - (B + C) := by 
      linarith [hABC]
    have h8 : sin A = sin (B + C) := by 
      rw [h7]
      have h9 : sin (π - (B + C)) = sin (B + C) := by 
        rw [sin_pi_sub]
      linarith [h9]
    rw [h8]
    have h9 : sin (B + C) = sin B * cos C + cos B * sin C := by
      rw [sin_add]
    rw [h9]
    have h5 : sin B > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h6 : sin C > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h5' : cos B < 1 := by 
      have h7 : B > 0 := hB1
      have h8 : B < π := hB2
      have h9 : cos B < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h6' : cos C < 1 := by 
      have h7 : C > 0 := hC1
      have h8 : C < π := hC2
      have h9 : cos C < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h7 : 1 - cos C > 0 := by 
      linarith [h6']
    have h8 : 1 - cos B > 0 := by 
      linarith [h5']
    have h9 : sin B * (1 - cos C) > 0 := by 
      apply mul_pos
      linarith [h5]
      linarith [h6']
    have h10 : sin C * (1 - cos B) > 0 := by 
      apply mul_pos
      linarith [h6]
      linarith [h5']
    nlinarith [h9, h10]
  -- Prove the third inequality: $\sin A + \sin C > \sin B$
  have h5 : sin A + sin C > sin B := by
    have h8 : B = π - (A + C) := by 
      linarith [hABC]
    have h9 : sin B = sin (A + C) := by 
      rw [h8]
      have h10 : sin (π - (A + C)) = sin (A + C) := by 
        rw [sin_pi_sub]
      linarith [h10]
    rw [h9]
    have h10 : sin (A + C) =  sin A * cos C + cos A * sin C := by 
      rw [sin_add]
    rw [h10]
    have h5 : sin A > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h6 : sin C > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals 
        linarith
    have h5' : cos A < 1 := by 
      have h7 : A > 0 := hA1
      have h8 : A < π := hA2
      have h9 : cos A < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h6' : cos C < 1 := by 
      have h7 : C > 0 := hC1
      have h8 : C < π := hC2
      have h9 : cos C < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals 
          linarith
      have h10 : cos (0 : ℝ) = 1 := by 
        simp
      linarith [h10, h9]
    have h7 : 1 - cos C > 0 := by 
      linarith [h6']
    have  h8 : 1 - cos A > 0 := by 
      linarith [h5']
    have h9 : sin A * (1 - cos C) > 0 := by 
      apply  mul_pos
      linarith [h5]
      linarith [h6']
    have h10 : sin C * (1 - cos A) > 0 := by 
      apply  mul_pos
      linarith [h6]
      linarith [h5']
    nlinarith [h9, h10]
  constructor
  · exact h3
  constructor
  · exact h4
  · exact h5