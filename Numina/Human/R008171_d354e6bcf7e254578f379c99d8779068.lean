import Mathlib

theorem calculus_13675 : Real.sin (11 * Real.pi / 3) = -Real.sqrt 3 / 2 := by 
  have h1 : Real.sin (11 * Real.pi / 3) = Real.sin (5 * Real.pi / 3) := by 
    have h1 : 11 * Real.pi / 3 = 5 * Real.pi / 3 + 2 * Real.pi := by ring
    rw [h1]
    rw [Real.sin_add_two_pi]
  have h2 : Real.sin (5 * Real.pi / 3) = -Real.sqrt 3 / 2 := by 
    have h1 : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by ring
    rw [h1]
    rw [Real.sin_two_pi_sub]
    rw [Real.sin_pi_div_three]
    ring
  rw [h1, h2]