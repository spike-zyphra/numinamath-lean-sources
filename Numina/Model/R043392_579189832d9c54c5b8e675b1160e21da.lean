import Mathlib

open Real Set
open scoped Real

theorem inequalities_252224 (x : Real) (hx : 0 < x ∧ x < π/2) :
    (1 + 1/sin x) * (1 + 1/cos x) ≥ 3 + 2*sqrt 2 := by
  have h1 : 0 < x := hx.1
  have h2 : x < π / 2 := hx.2
  have h3 : 0 < sin x := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, Real.pi_pos]
    linarith [h2, Real.pi_pos]

  have h4 : 0 < cos x := by
    have h5 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    linarith

  have h9 : (1 + 1/sin x) * (1 + 1/cos x) - (3 + 2 * sqrt 2) ≥ 0 := by
    have h10 : 0 < sin x * cos x := mul_pos h3 h4
    have h11 : (1 + 1/sin x) * (1 + 1/cos x) - (3 + 2 * sqrt 2) = 
      ( (sin x + 1) * (cos x + 1) - (3 + 2 * sqrt 2) * (sin x * cos x) ) / (sin x * cos x):= by
      field_simp [h3, h4]
      <;> ring 
    rw [h11]
    apply div_nonneg
    · -- Show that numerator is non-negative
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x - Real.sqrt 2), sq_nonneg ((sin x) * (cos x) - 1 / 2), sq_nonneg (sin x - cos x), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sin_sq_add_cos_sq x, mul_pos h3 h4]
    · -- Show that denominator is positive
      positivity

  linarith