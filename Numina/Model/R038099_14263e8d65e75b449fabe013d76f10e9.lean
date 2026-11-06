import Mathlib

theorem calculus_22444 (x y z : ℝ) (hx : Real.cos x + Real.cos y + Real.cos z = 0) (hy : Real.sin x + Real.sin y + Real.sin z = 0) :
    Real.cos (2 * x - y - z) = 1 := by 
  have h1 : Real.cos z = -Real.cos x - Real.cos y := by linarith 
  have h2 : Real.sin z = -Real.sin x - Real.sin y := by linarith
  have h_eq : (Real.cos x + Real.cos y) ^ 2 + (Real.sin x + Real.sin y) ^ 2 = 1 := by 
    have h1' : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z 
    rw [show Real.cos z = - (Real.cos x + Real.cos y) by linarith [h1], show Real.sin z = - (Real.sin x + Real.sin y) by linarith [h2]] at h1' 
    nlinarith 
  have h_eq2 : Real.cos x * Real.cos y + Real.sin x * Real.sin y = -1 / 2 := by 
    nlinarith [Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y, h_eq]
  have h5 : Real.cos (2 * x - y - z) = Real.cos (2 * x) * Real.cos (y + z) + Real.sin (2 * x) * Real.sin (y + z) := by 
    rw [show 2 * x - y - z = 2 * x - (y + z) by ring]
    rw [Real.cos_sub]
  have h6 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h7 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have h8 : Real.cos (y + z) = Real.cos y * Real.cos z - Real.sin y * Real.sin z := by 
    rw [Real.cos_add]
  have h9 : Real.sin (y + z) = Real.sin y * Real.cos z + Real.cos y * Real.sin z := by 
    rw [Real.sin_add]
  rw [h5, h6, h7, h8, h9, h1, h2]
  have h_eq3 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x 
  have h_eq4 : Real.cos y ^ 2 + Real.sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y 
  nlinarith [sq_nonneg (Real.cos x - Real.cos y), sq_nonneg (Real.sin x - Real.sin y), sq_nonneg (Real.cos x + Real.cos y), sq_nonneg (Real.sin x + Real.sin y), Real.cos_sq_add_sin_sq x, Real.cos_sq_add_sin_sq y]