import Mathlib

open Real

theorem inequalities_109058 (a : ℝ) (ha : ∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) :
    a ≥ sqrt 2 := by

  have h1 := ha 1 1 (by norm_num) (by norm_num)
  have h2 : sqrt (1 : ℝ) = 1 := by
    simp [sqrt_eq_iff_sq_eq]
  have h3 : sqrt (1 + (1 : ℝ)) = Real.sqrt 2 := by
    norm_num
  rw [h2] at h1
  rw [h3] at h1
  have h4 : (2 : ℝ) ≤ a * Real.sqrt 2 := by
    nlinarith [show (0 : ℝ) < (1 : ℝ) by norm_num, show (0 : ℝ) < (1 : ℝ) by norm_num, Real.sqrt_nonneg 1, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  by_contra h
  push_neg at h
  have h5 : a < Real.sqrt 2 := by linarith
  have h6 : a * Real.sqrt 2 < (2 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h5]
  nlinarith [h4, h6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]