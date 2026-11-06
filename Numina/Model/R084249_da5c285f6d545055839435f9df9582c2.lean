import Mathlib

theorem algebra_186168 : (Real.sin (Real.pi / 8))^2 + (Real.cos (3 * Real.pi / 8))^2 +
    (Real.sin (5 * Real.pi / 8))^2 + (Real.cos (7 * Real.pi / 8))^2 = 2 := by 
  have h1 : Real.sin (5 * Real.pi / 8) = Real.sin (3 * Real.pi / 8) := by 
    have h2 : 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [Real.sin_pi_sub]
  have h3 : Real.cos (7 * Real.pi / 8) = - Real.cos (Real.pi / 8) := by 
    have h4 : 7 * Real.pi / 8 = Real.pi - Real.pi / 8 := by
      linarith [Real.pi_pos]
    rw [h4]
    rw [Real.cos_pi_sub]
  rw [h1, h3]
  have h5 : (Real.sin (Real.pi / 8))^2 + (Real.cos (Real.pi / 8))^2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (Real.pi / 8)
  have h6 : (Real.sin (3 * Real.pi / 8))^2 + (Real.cos (3 * Real.pi / 8))^2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (3 * Real.pi / 8)
  nlinarith [Real.sin_sq_add_cos_sq (3 * Real.pi / 8), Real.sin_sq_add_cos_sq (Real.pi / 8), h5, h6]