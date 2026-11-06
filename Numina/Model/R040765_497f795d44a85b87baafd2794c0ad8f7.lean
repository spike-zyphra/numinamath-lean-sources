import Mathlib

open Real

theorem algebra_159649 {b : ℝ} (hb : b > 2) :
    ((b^2 - 3 * b - (b - 1) * sqrt (b^2 - 4) + 2) /
     (b^2 + 3 * b - (b + 1) * sqrt (b^2 - 4) + 2)) *
    sqrt ((b + 2) / (b - 2)) = (1 - b) / (1 + b) := by

  have h1 : b - 2 > 0 := by linarith
  have h2 : b + 2 > 0 := by linarith
  
  have h3 : sqrt (b^2 - 4) = Real.sqrt (b - 2) * Real.sqrt (b + 2) := by
    have h4 : b^2 - 4 = (b - 2) * (b + 2) := by ring
    rw [h4]
    rw [Real.sqrt_mul]
    all_goals linarith
  
  have numer_eq : b^2 - 3 * b - (b - 1) * sqrt (b^2 - 4) + 2 = (b - 1) * (b - 2 - Real.sqrt (b^2 - 4)) := by 
    ring
  
  have denom_eq : b^2 + 3 * b - (b + 1) * sqrt (b^2 - 4) + 2 = (b + 1) * (b + 2 - Real.sqrt (b^2 - 4)) := by 
    ring
  
  rw [numer_eq, denom_eq]

  have h5 : Real.sqrt (b^2 - 4) = Real.sqrt (b - 2) * Real.sqrt (b + 2) := h3
  
  have h6 : b - 2 - Real.sqrt (b^2 - 4) = Real.sqrt (b - 2) * (Real.sqrt (b - 2) - Real.sqrt (b + 2)) := by
    rw [h5]
    have h7 : Real.sqrt (b - 2) ^ 2 = b - 2 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (b - 2), Real.sqrt_nonneg (b + 2)]
  
  have h8 : b + 2 - Real.sqrt (b^2 - 4) = Real.sqrt (b + 2) * (Real.sqrt (b + 2) - Real.sqrt (b - 2)) := by
    rw [h5]
    have h9 : Real.sqrt (b + 2) ^ 2 = b + 2 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [Real.sqrt_nonneg (b - 2), Real.sqrt_nonneg (b + 2)]
  
  rw [h6, h8]

  have h10 : Real.sqrt (b - 2) - Real.sqrt (b + 2) = - (Real.sqrt (b + 2) - Real.sqrt (b - 2)) := by 
    ring
  
  rw [h10]

  have sqrt_div : sqrt ((b + 2) / (b - 2)) = Real.sqrt (b + 2) / Real.sqrt (b - 2) := by
    field_simp [Real.sqrt_div]
    all_goals linarith

  rw [sqrt_div]

  have h11 : Real.sqrt (b + 2) - Real.sqrt (b - 2) ≠ 0 := by
    have h12 : Real.sqrt (b + 2) > 0 := by 
      apply Real.sqrt_pos.mpr
      linarith
    have h13 : Real.sqrt (b - 2) > 0 := by 
      apply Real.sqrt_pos.mpr
      linarith
    by_contra h
    have h14 : Real.sqrt (b + 2) = Real.sqrt (b - 2) := by linarith
    have h15 : Real.sqrt (b + 2) ^ 2 = Real.sqrt (b - 2) ^ 2 := by rw [h14]
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at h15
    nlinarith
  
  field_simp [h11]
  <;> nlinarith [Real.sqrt_pos.mpr h1, Real.sqrt_pos.mpr h2, Real.sq_sqrt (show (0 : ℝ) ≤ b - 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b + 2 by linarith), Real.sqrt_nonneg (b - 2), Real.sqrt_nonneg (b + 2)]