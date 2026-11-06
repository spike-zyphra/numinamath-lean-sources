import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_240106 (x : ℝ) :
  1 / 8 ≤ (cos x)^8 + (sin x)^8 ∧ (cos x)^8 + (sin x)^8 ≤ 1 := by
  have h1 : cos x ^ 2 + sin x ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq x

  have h2 : (cos x) ^ 8 + (sin x) ^ 8 = 1 - 4 * (cos x ^ 2 * sin x ^ 2) + 2 * (cos x ^ 2 * sin x ^ 2) ^ 2 := by
    have h3 : (cos x) ^ 4 + (sin x) ^ 4 = 1 - 2 * (cos x ^ 2 * sin x ^ 2) := by
      have h4 : (cos x) ^ 4 + (sin x) ^ 4 = ((cos x ^ 2 + sin x ^ 2) )^2 - 2 * (cos x ^ 2 * sin x ^ 2) := by
        ring
      rw [h4, h1]
      all_goals ring
    have h5 : (cos x) ^ 8 + (sin x) ^ 8 = ((cos x) ^ 4 + (sin x) ^ 4) ^ 2 - 2 * (cos x ^ 2 * sin x ^ 2) ^ 2 := by 
      ring
    rw [h5, h3]
    all_goals ring_nf
    all_goals nlinarith [h1]

  have h3 : 1 / 8 ≤ (cos x) ^ 8 + (sin x) ^ 8 := by
    have h5 : (cos x ^ 2 * sin x ^ 2) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (cos x ^ 2 * sin x ^ 2), sq_nonneg (cos x ^ 2 - sin x ^ 2), h1, sq_nonneg (cos x ^ 2 * sin x ^ 2 - (1 / 4)), mul_nonneg (show (0 : ℝ) ≤ cos x ^ 2 by nlinarith [sq_nonneg (cos x), h1]) (show (0 : ℝ) ≤ sin x ^ 2 by nlinarith [sq_nonneg (sin x), h1])]
    have h6 : (cos x ^ 2 * sin x ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (cos x ^ 2), sq_nonneg (sin x ^ 2), h1, sq_nonneg (cos x ^ 2 * sin x ^ 2)]
    rw [show (cos x) ^ 8 + (sin x) ^ 8 = 1 - 4 * (cos x ^ 2 * sin x ^ 2) + 2 * (cos x ^ 2 * sin x ^ 2) ^ 2 by linarith [h2]]
    nlinarith [sq_nonneg (cos x ^ 2 * sin x ^ 2 - 1 / 4), sq_nonneg (cos x ^ 2 * sin x ^ 2 - 0 ), sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg ((cos x ^ 2 * sin x ^ 2) ^ 2 ), h1, h5, h6, mul_nonneg (show (0 : ℝ) ≤ cos x ^ 2 by nlinarith [sq_nonneg (cos x), h1]) (show (0 : ℝ) ≤ sin x ^ 2 by nlinarith [sq_nonneg (sin x), h1]), sq_nonneg (cos x^2 ), sq_nonneg (sin x^2)]

  have h4 : (cos x) ^ 8 + (sin x) ^ 8 ≤ 1 := by
    have h5 : (cos x ^ 2 * sin x ^ 2) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (cos x ^ 2 * sin x ^ 2), sq_nonneg (cos x ^ 2 - sin x ^ 2), h1, sq_nonneg (cos x ^ 2 * sin x ^ 2 - (1 / 4)), mul_nonneg (show (0 : ℝ) ≤ cos x ^ 2 by nlinarith [sq_nonneg (cos x), h1]) (show (0 : ℝ) ≤ sin x ^ 2 by nlinarith [sq_nonneg (sin x), h1])]
    have h6 : (cos x ^ 2 * sin x ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (cos x ^ 2), sq_nonneg (sin x ^ 2), h1, sq_nonneg (cos x ^ 2 * sin x ^ 2)]
    rw [show (cos x) ^ 8 + (sin x) ^ 8 = 1 - 4 * (cos x ^ 2 * sin x ^ 2) + 2 * (cos x ^ 2 * sin x ^ 2) ^ 2 by linarith [h2]]
    nlinarith [sq_nonneg (cos x ^ 2 * sin x ^ 2 - 1 / 2), sq_nonneg ((cos x ^ 2 * sin x ^ 2) ^ 2 ), sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg (cos x ^ 2 * sin x ^ 2 - 1 / 4), h1, h5, h6, mul_nonneg (show (0 : ℝ) ≤ cos x ^ 2 by nlinarith [sq_nonneg (cos x), h1]) (show (0 : ℝ) ≤ sin x ^ 2 by nlinarith [sq_nonneg (sin x), h1]), sq_nonneg (cos x^2 ), sq_nonneg (sin x^2)]
  
  constructor
  · linarith [h3]
  · linarith [h4]