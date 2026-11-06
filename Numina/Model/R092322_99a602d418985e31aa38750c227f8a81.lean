import Mathlib

theorem calculus_22951 : Real.sin (4 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
  have h1 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by
    linarith [Real.pi_pos]
  rw [h1]
  rw [Real.sin_add]
  have h2 : Real.sin Real.pi = 0 := Real.sin_pi
  have h3 : Real.cos Real.pi = -1 := Real.cos_pi
  have h4 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  rw [h2, h3, h4, h5]
  ring