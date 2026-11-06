import Mathlib

theorem inequalities_305050 (x : Fin 2 → ℝ) (hx : ∀ i, 0 < x i) (k : ℝ)
    (h : x 0 * x 1 = k) :
    x 0 + x 1 ≥ 2 * Real.sqrt k := by
  have hx0_pos : 0 < x 0 := hx 0
  have hx1_pos : 0 < x 1 := hx 1

  have h1 : (Real.sqrt (x 0) - Real.sqrt (x 1)) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  
  have h2 : (Real.sqrt (x 0) - Real.sqrt (x 1)) ^ 2 = (Real.sqrt (x 0)) ^ 2 + (Real.sqrt (x 1)) ^ 2 - 2 * (Real.sqrt (x 0) * Real.sqrt (x 1)) := by 
    ring
  
  have h3 : (Real.sqrt (x 0)) ^ 2 = x 0 := by 
    rw [Real.sq_sqrt]
    linarith
  
  have h4 : (Real.sqrt (x 1)) ^ 2 = x 1 := by 
    rw [Real.sq_sqrt]
    linarith
  
  have h5 : Real.sqrt (x 0) * Real.sqrt (x 1) = Real.sqrt (x 0 * x 1) := by 
    rw [← Real.sqrt_mul (by positivity)]
  
  have h6 : x 0 * x 1 = k := h
  
  have h7 : Real.sqrt (x 0 * x 1) = Real.sqrt k := by 
    rw [h6]
  
  -- Now, x 0 + x 1 - 2 * sqrt(k) ≥ 0
  nlinarith [h1, h2, h3, h4, h5, h7, Real.sqrt_nonneg k, Real.sq_sqrt (show 0 ≤ k by nlinarith [h6, hx0_pos, hx1_pos]), Real.sqrt_nonneg (x 0 * x 1), Real.sqrt_nonneg (x 0), Real.sqrt_nonneg (x 1)]