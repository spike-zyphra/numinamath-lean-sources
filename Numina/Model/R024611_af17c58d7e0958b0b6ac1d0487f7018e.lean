import Mathlib

open Real
open scoped Real

theorem inequalities_187783 (A B C : Real) (hA : A ∈ Set.Ioo 0 (π / 2)) (hB : B ∈ Set.Ioo 0 (π / 2))
    (hC : C ∈ Set.Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    sin A + sin B + sin C > cos A + cos B + cos C := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : A + B > π / 2 := by
    linarith [hABC, hC1, hC2, Real.pi_pos]
  have h2 : sin A > cos B := by
    have h3 : A > π / 2 - B := by
      linarith [h1]
    have h4 : sin A > sin (π / 2 - B) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [hA1, hA2, hB1, hB2, Real.pi_pos]
    have h5 : sin (π / 2 - B) = cos B := by
      rw [show π / 2 - B = π / 2 - B by rfl]
      rw [sin_pi_div_two_sub]
    linarith [h4, h5]
  have h3 : B + C > π / 2 := by
    linarith [hABC, hA1, hA2, Real.pi_pos]
  have h3' : sin B > cos C := by
    have h4 : B > π / 2 - C := by
      linarith [h3]
    have h5 : sin B > sin (π / 2 - C) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [hB1, hB2, hC1, hC2, Real.pi_pos]
    have h6 : sin (π / 2 - C) = cos C := by
      rw [show π / 2 - C = π / 2 - C by rfl]
      rw [sin_pi_div_two_sub]
    linarith [h5, h6]
  have h4 : A + C > π / 2 := by
    linarith [hABC, hB1, hB2, Real.pi_pos]
  have h4' : sin C > cos A := by
    have h5 : C > π / 2 - A := by
      linarith [h4]
    have h6 : sin C > sin (π / 2 - A) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        nlinarith [hC1, hC2, hA1, hA2, Real.pi_pos]
    have h7 : sin (π / 2 - A) = cos A := by
      rw [show π / 2 - A = π / 2 - A by rfl]
      rw [sin_pi_div_two_sub]
    linarith [h6, h7]
  linarith [h2, h3', h4']