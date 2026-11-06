import Mathlib

theorem calculus_13675 : Real.sin (11 * Real.pi / 3) = -Real.sqrt 3 / 2 := by
  have h1 : Real.sin (11 * Real.pi / 3) = Real.sin (5 * Real.pi / 3) := by
    have h2 : 11 * Real.pi / 3 = 5 * Real.pi / 3 + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.sin_add_two_pi]
  rw [h1]
  have h3 : Real.sin (5 * Real.pi / 3) = -Real.sin (Real.pi / 3) := by
    have h4 : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by 
      linarith [Real.pi_pos]
    rw [h4]
    rw [Real.sin_two_pi_sub]
  rw [h3]
  rw [Real.sin_pi_div_three]
  ring