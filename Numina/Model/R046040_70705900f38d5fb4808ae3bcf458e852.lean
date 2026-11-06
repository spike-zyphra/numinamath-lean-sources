import Mathlib

open Real Set
open scoped Real

theorem algebra_282019 (α : Real) :
  sin (π / 4 - α) - cos (π / 6 + α) + sin (π / 6) ^ 2 -
  cos (π / 4 + α) + sin (π / 3 - α) + sin (π / 3) ^ 2 = 1 := by
  have h1 : sin (π / 4 - α) = sin (π / 4) * cos α - cos (π / 4) * sin α := by
    rw [sin_sub]
  have h2 : cos (π / 6 + α) = cos (π / 6) * cos α - sin (π / 6) * sin α := by 
    rw [cos_add]
  have h3 : sin (π / 6) = 1 / 2 := by
    exact sin_pi_div_six
  have h4 : sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h5 : cos (π / 4 + α) = cos (π / 4) * cos α - sin (π / 4) * sin α := by
    rw [cos_add]
  have h6 : sin (π / 3 - α) = sin (π / 3) * cos α - cos (π / 3) * sin α := by
    rw [sin_sub]
  have h7 : cos (π / 4) = Real.sqrt 2 / 2 := by
    have h1 : cos (π / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    exact h1
  have h8 : sin (π / 4) = Real.sqrt 2 / 2 := by
    exact sin_pi_div_four
  have h9 : cos (π / 6) = Real.sqrt 3 / 2 := by
    exact cos_pi_div_six
  have h10 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  rw [h1, h2, h3, h5, h6, h4, h7, h8, h9, h10]
  have h11 : Real.sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by linarith)
  have h12 : Real.sqrt 3 ^ 2 = 3 := by
    exact Real.sq_sqrt (by linarith)
  ring_nf
  <;> simp [h11, h12]
  <;> nlinarith