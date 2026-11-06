import Mathlib

open Real

theorem inequalities_6758 {x : ℝ} (hx : 1 ≤ x) (h : x + 1 / x < sqrt 5) :
    1 ≤ x ∧ x < (sqrt 5 + 1) / 2 := by
  have h1 : x > 0 := by linarith
  have h' : x^2 + 1 < x * sqrt 5 := by
    have h2 : x > 0 := by linarith
    have h' : (x + 1 / x) < sqrt 5 := h
    have h3 : x^2 + 1 = x * (x + 1 / x) := by
      field_simp
      <;> ring_nf <;> norm_num
    rw [h3]
    have h4 : x * (x + 1 / x) < x * (sqrt 5) := by
      apply mul_lt_mul_of_pos_left
      linarith
      linarith
    nlinarith
  have h5 : x^2 - x * sqrt 5 + 1 < 0 := by 
    nlinarith
  have h6 : x < (sqrt 5 + 1) / 2 := by
    nlinarith [ Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ), sq_nonneg (x - (sqrt 5 + 1)/2), sq_nonneg (x - (sqrt 5 - 1)/2) ]
  constructor
  · linarith
  · linarith