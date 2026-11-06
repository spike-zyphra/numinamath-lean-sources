import Mathlib

open Real

theorem inequalities_300867 (a : ℝ) (ha : ∀ x y : ℝ, x > 0 → y > 0 → sqrt x + sqrt y ≤ a * sqrt (x + y)) :
    a ≥ sqrt 2 := by
  have h1 := ha 1 1 (by norm_num) (by norm_num)
  have h2 : sqrt (1 : ℝ) = 1 := by
    rw [sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : sqrt ((1 : ℝ) + (1 : ℝ)) = Real.sqrt 2 := by
    norm_num
  rw [h2] at h1
  rw [h3] at h1
  have h4 : Real.sqrt 2 > 0 := by
    positivity
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]