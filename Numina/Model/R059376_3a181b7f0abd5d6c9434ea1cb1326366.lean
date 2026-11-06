import Mathlib

open Real

theorem algebra_97405 : 2 + sqrt 2 + 1 / (2 + sqrt 2) + 1 / (sqrt 2 - 2) = 2 := by
  have h1 : sqrt 2 > 0 := by positivity
  have h2 : sqrt 2 - 2 ≠ 0 := by
    by_contra h
    have h3 : sqrt 2 = 2 := by linarith
    have h4 : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
    nlinarith [Real.sqrt_nonneg 2, show (sqrt 2) > 0 by positivity, h3]
  have h3 : (2 + sqrt 2) ≠ 0 := by positivity
  field_simp [h3, h2, show sqrt 2 + 2 ≠ 0 by positivity, show sqrt 2 - 2 ≠ 0 by exact h2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  <;> ring_nf <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]