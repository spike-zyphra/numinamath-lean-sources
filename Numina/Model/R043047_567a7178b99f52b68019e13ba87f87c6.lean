import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_107004 (x : ℝ) (hx : x ≥ -6) :
    x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6) ↔ x ∈ Icc (-5) 3 := by
  constructor
  · -- Assume x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6), prove x ∈ Icc (-5) 3
    intro h
    have h1 : sqrt (x + 6) ≥ 0 := by positivity
    have h2 : x + 6 ≥ 0 := by linarith
    have h3 : (sqrt (x + 6)) ^ 2 = x + 6 := by
      rw [Real.sq_sqrt]
      linarith
    constructor
    · -- Show that -5 ≤ x
      nlinarith [ sq_nonneg (x + 5), sq_nonneg (x - 3), sq_nonneg (sqrt (x + 6) - 1), sq_nonneg (sqrt (x + 6) - 3), 
        Real.sqrt_nonneg (x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 by linarith)]
    · -- Show that x ≤ 3
      nlinarith [ sq_nonneg (x + 5), sq_nonneg (x - 3), sq_nonneg (sqrt (x + 6) - 1), sq_nonneg (sqrt (x + 6) - 3), 
        Real.sqrt_nonneg (x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 by linarith)]
  · -- Assume x ∈ Icc (-5) 3, prove x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6)
    rintro ⟨h1, h2⟩
    have h3 : sqrt (x + 6) ≥ 0 := by positivity
    have h4 : sqrt (x + 6) ≥ 1 := by
      nlinarith [ Real.sqrt_nonneg (x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 by linarith), h1 ]
    have h5 : sqrt (x + 6) ≤ 3 := by
      nlinarith [ Real.sqrt_nonneg (x + 6), Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 by linarith), h2 ]
    nlinarith [ sq_nonneg (x - 3), sq_nonneg (x + 5), sq_nonneg (sqrt (x + 6) - 1), sq_nonneg (sqrt (x + 6) - 3), 
      mul_nonneg (Real.sqrt_nonneg (x + 6)) (Real.sqrt_nonneg (x + 6)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x + 6 by linarith)
    ]