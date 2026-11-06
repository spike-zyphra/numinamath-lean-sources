import Mathlib

open Real Set
open scoped Real

theorem inequalities_305159 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    sin A + sin B + sin C > cos A + cos B + cos C := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h3 : sin A > cos B := by
    have h4 : A > π / 2 - B := by
      have h5 : A + B > π / 2 := by
        have h6 : C < π / 2 := by linarith
        nlinarith [hABC]
      linarith
    have h7 : sin A > sin (π / 2 - B) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith
    have h8 : sin (π / 2 - B) = cos B := by
      rw [sin_pi_div_two_sub]
    linarith
  have h3' : sin B > cos C := by
    have h4 : B > π / 2 - C := by
      have h5 : B + C > π / 2 := by
        have h6 : A < π / 2 := by linarith
        nlinarith [hABC]
      linarith
    have h7 : sin B > sin (π / 2 - C) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith
    have h8 : sin (π / 2 - C) = cos C := by
      rw [sin_pi_div_two_sub]
    linarith
  have h3'' : sin C > cos A := by
    have h4 : C > π / 2 - A := by
      have h5 : A + C > π / 2 := by
        have h6 : B < π / 2 := by linarith
        nlinarith [hABC]
      linarith
    have h7 : sin C > sin (π / 2 - A) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith
    have h8 : sin (π / 2 - A) = cos A := by
      rw [sin_pi_div_two_sub]
    linarith
  linarith [h3, h3', h3'']