import Mathlib

open Real Set
open scoped Real

theorem algebra_153726 : 3 * sin (π / 3) - 2 * cos (π / 6) + 3 * tan (π / 3) - 4 / tan (π / 2) = 7 * sqrt 3 / 2 := by 
  have h1 : sin (π / 3) = sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h2 : cos (π / 6) = sqrt 3 / 2 := by
    exact cos_pi_div_six
  have h3 : tan (π / 3) = sqrt 3 := by
    rw [tan_pi_div_three]
  have h4 : tan (π / 2) = 0 := by
    rw [tan_pi_div_two]
  rw [h1, h2, h3, h4]
  ring