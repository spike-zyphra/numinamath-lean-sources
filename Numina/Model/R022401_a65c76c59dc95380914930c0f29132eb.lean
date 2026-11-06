import Mathlib

theorem algebra_147946 (a : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = Real.sin (2 * x) + a * Real.cos (2 * x))
    (h : ∀ x, f (-Real.pi / 6 + x) = f (-Real.pi / 6 - x)) :
    a = -Real.sqrt 3 / 3 := by
  have eq1 := h (Real.pi / 6)
  have eq2 : f (-Real.pi / 6 + Real.pi / 6) = f (-Real.pi / 6 - Real.pi / 6) := eq1
  have eq3 : f (-Real.pi / 6 + Real.pi / 6) = f 0 := by ring_nf
  have eq4 : f (-Real.pi / 6 - Real.pi / 6) = f (-Real.pi / 3) := by ring_nf
  rw [eq3] at eq2
  rw [eq4] at eq2
  have eq5 : f 0 = Real.sin (2 * (0 : ℝ)) + a * Real.cos (2 * (0 : ℝ)) := hf 0
  have eq6 : f (-Real.pi / 3) = Real.sin (2 * (-Real.pi / 3 : ℝ)) + a * Real.cos (2 * (-Real.pi / 3 : ℝ)) := hf (-Real.pi / 3)
  rw [eq5] at eq2
  rw [eq6] at eq2
  have h1 : Real.sin (2 * (0 : ℝ)) = 0 := by
    simp [Real.sin_zero]
  have h2 : Real.cos (2 * (0 : ℝ)) = 1 := by
    simp [Real.cos_zero]
  have h3 : Real.sin (2 * (-Real.pi / 3 : ℝ)) = - Real.sqrt 3 / 2 := by
    have h3a : 2 * (-Real.pi / 3 : ℝ) = - (2 * Real.pi / 3) := by ring
    rw [h3a]
    have h3b : Real.sin (- (2 * Real.pi / 3 : ℝ)) = - Real.sin (2 * Real.pi / 3 : ℝ) := by
      rw [Real.sin_neg]
    have h3c : Real.sin (2 * Real.pi / 3 : ℝ) = Real.sqrt 3 / 2 := by
      have h3d : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3 : ℝ) := by ring
      rw [h3d]
      rw [Real.sin_pi_sub]
      have h3e : Real.sin (Real.pi / 3 : ℝ) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith [h3e]
    rw [h3b, h3c]
    all_goals linarith
  have h4 : Real.cos (2 * (-Real.pi / 3 : ℝ)) = -1 / 2 := by
    have h4a : 2 * (-Real.pi / 3 : ℝ) = - (2 * Real.pi / 3) := by ring
    rw [h4a]
    have h4b : Real.cos (- (2 * Real.pi / 3 : ℝ)) = Real.cos (2 * Real.pi / 3 : ℝ) := by
      rw [Real.cos_neg]
    have h4c : Real.cos (2 * Real.pi / 3 : ℝ) = -1 / 2 := by
      have h4d : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3 : ℝ) := by ring
      rw [h4d]
      rw [Real.cos_pi_sub]
      have h4e : Real.cos (Real.pi / 3 : ℝ) = 1 / 2 := Real.cos_pi_div_three
      linarith [h4e]
    rw [h4b, h4c]
    all_goals linarith
  rw [h1, h2, h3, h4] at eq2
  ring_nf at eq2
  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]