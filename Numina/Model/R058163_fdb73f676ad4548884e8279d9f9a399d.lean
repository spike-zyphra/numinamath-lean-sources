import Mathlib

theorem algebra_318288 (f : ℝ → ℝ) (k : ℝ) (hf : f = fun x => x^2 - (k + 1)*x + 2)
    (h : ∀ x > 0, f x > 0) :
    k < 2 * Real.sqrt 2 - 1 := by
  by_contra h1
  push_neg at h1
  have h2 : k + 1 ≥ 2 * Real.sqrt 2 := by linarith 
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h4 : (2 * Real.sqrt 2)^2 = 8 := by 
      calc
        (2 * Real.sqrt 2)^2 = 4 * Real.sqrt 2 ^ 2 := by ring
        _ = 4 * 2 := by rw [h3]
        _ = 8 := by norm_num
  have h5 : (k + 1)^2 ≥ 8 := by
    have h6 : k + 1 ≥ 2 * Real.sqrt 2 := by linarith
    have h7 : (k + 1)^2 ≥ (2 * Real.sqrt 2)^2 := by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h3]
  
  -- Applying h at x = (k + 1)/2 > 0

  have hx_pos : (k + 1) / 2 > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg 2]

  have hfx : f ((k + 1) / 2) = ((k + 1) / 2) ^ 2 - (k + 1) * ((k + 1) / 2) + 2 := by 
    rw [hf]

  have hfx_nonpos : f ((k + 1) / 2) ≤ 0 := by 
    rw [hfx]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h3]

  have h_pos : f ((k + 1) / 2) > 0 := h ((k + 1) / 2) hx_pos

  -- Contradiction than f((k+1)/2) ≤ 0 and f((k+1)/2) > 0
  linarith