import Mathlib

theorem algebra_153846 : Real.sin (53 * Real.pi / 6) = 1 / 2 := by

  have h1 : 53 * Real.pi / 6 = 2 * Real.pi * 4 + 5 * Real.pi / 6 := by 
    linarith [Real.pi_pos]
  
  rw [h1]
  have h2 : Real.sin (2 * Real.pi * 4 + 5 * Real.pi / 6) = Real.sin (5 * Real.pi / 6) := by 
    have h5 : 2 * Real.pi * 4 + 5 * Real.pi / 6 = (5 * Real.pi / 6) + (4 : ℕ) * (2 * Real.pi) := by 
      ring 
    rw [h5]
    rw [Real.sin_add_nat_mul_two_pi]
  
  rw [h2]
  have h3 : Real.sin (5 * Real.pi / 6) = 1 / 2 := by 
    have h4 : 5 * Real.pi / 6 = Real.pi - Real.pi / 6 := by 
      linarith [Real.pi_pos]
    rw [h4]
    have h5 : Real.sin (Real.pi - Real.pi / 6) = Real.sin (Real.pi / 6) := by 
      rw [Real.sin_pi_sub]
    rw [h5]
    have h6 : Real.sin (Real.pi / 6) = 1 / 2 := by 
      exact Real.sin_pi_div_six
    linarith [h6]

  exact h3