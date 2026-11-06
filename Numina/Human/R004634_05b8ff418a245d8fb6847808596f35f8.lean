import Mathlib

open Real Set
open scoped Real

theorem inequalities_291878 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    sin A + sin B + sin C > cos A + cos B + cos C := by
  have h1 : sin A > cos B := by
    have hA1 : 0 < A := hA.left
    have hA2 : A < π / 2 := hA.right
    have hB1 : 0 < B := hB.left
    have hB2 : B < π / 2 := hB.right
    have hC1 : 0 < C := hC.left
    have hC2 : C < π / 2 := hC.right
    have hAB : A + B > π / 2 := by linarith [hABC, hC1, Real.pi_pos]
    have hsin : sin A > sin (π / 2 - B) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith
    rw [Real.sin_pi_div_two_sub] at hsin
    linarith
  have h2 : sin B > cos C := by
    have hA1 : 0 < A := hA.left
    have hA2 : A < π / 2 := hA.right
    have hB1 : 0 < B := hB.left
    have hB2 : B < π / 2 := hB.right
    have hC1 : 0 < C := hC.left
    have hC2 : C < π / 2 := hC.right
    have hBC : B + C > π / 2 := by linarith [hABC, hA1, Real.pi_pos]
    have hsin : sin B > sin (π / 2 - C) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith
    rw [Real.sin_pi_div_two_sub] at hsin
    linarith
  have h3 : sin C > cos A := by
    have hA1 : 0 < A := hA.left
    have hA2 : A < π / 2 := hA.right
    have hB1 : 0 < B := hB.left
    have hB2 : B < π / 2 := hB.right
    have hC1 : 0 < C := hC.left
    have hC2 : C < π / 2 := hC.right
    have hAC : A + C > π / 2 := by linarith [hABC, hB1, Real.pi_pos]
    have hsin : sin C > sin (π / 2 - A) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith
    rw [Real.sin_pi_div_two_sub] at hsin
    linarith
  linarith