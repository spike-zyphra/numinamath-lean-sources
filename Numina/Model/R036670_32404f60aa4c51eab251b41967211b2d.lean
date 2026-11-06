import Mathlib

open Real Set
open scoped Real

theorem calculus_12463 : arcsin (1 / sqrt 2) = π / 4 := by

  have h1 : (1 / sqrt 2 : ℝ) = Real.sqrt 2 / 2 := by 
    field_simp
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  
  rw [h1]

  have h3 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
    have h12 : Real.sin (π / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    linarith [h12]

  have h2 : arcsin (Real.sqrt 2 / 2) = π / 4 := by
    have h5 : arcsin (Real.sqrt 2 / 2) = arcsin (Real.sin (π / 4)) := by 
      rw [h3]
    rw [h5]

    have h6 : -Real.pi / 2 ≤ (π / 4 : ℝ) := by 
      linarith [Real.pi_pos]

    have h7 : (π / 4 : ℝ) ≤ Real.pi / 2 := by 
      linarith [Real.pi_pos]

    have h8 : arcsin (Real.sin (π / 4)) = π / 4 := by 
      apply arcsin_sin
      all_goals
        linarith [Real.pi_pos]

    exact h8
  
  exact h2