import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307906 (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
  (hsum : u + v + w = 2) :
  u^2 * v^2 + v^2 * w^2 + w^2 * u^2 ∈ Icc 0 1 := by
  have h1 : 0 ≤ u ^ 2 * v ^ 2 := by positivity
  have h2 : 0 ≤ v ^ 2 * w ^ 2 := by positivity
  have h3 : 0 ≤ w ^ 2 * u ^ 2 := by positivity
  have h4 : 0 ≤ u ^ 2 * v ^ 2 + v ^ 2 * w ^ 2 + w ^ 2 * u ^ 2 := by 
    linarith
  have h5 : u ^ 2 * v ^ 2 + v ^ 2 * w ^ 2 + w ^ 2 * u ^ 2 ≤ 1 := by 
    have hw_eq : w = 2 - u - v := by linarith
    rw [hw_eq]
    nlinarith [sq_nonneg (u - 1), sq_nonneg (v - 1), sq_nonneg ((2 - u - v) - 1), 
      mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ v by linarith), 
      mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ (2 - u - v) by nlinarith), 
      mul_nonneg (show 0 ≤ (2 - u - v) by nlinarith) (show 0 ≤ u by linarith), 
      sq_nonneg (u + v - (2 - u - v)), 
      sq_nonneg (u - v), sq_nonneg (v - (2 - u - v)), sq_nonneg (u - (2 - u - v)), 
      mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ v by linarith), 
      mul_nonneg (show 0 ≤ v by linarith) (show 0 ≤ (2 - u - v) by nlinarith), 
      mul_nonneg (show 0 ≤ (2 - u - v) by nlinarith) (show 0 ≤ u by linarith)]
  constructor
  · -- Show that 0 ≤ u ^ 2 * v ^ 2 + v ^ 2 * w ^ 2 + w ^ 2 * u ^ 2
    linarith
  · -- Show that u ^ 2 * v ^ 2 + v ^ 2 * w ^ 2 + w ^ 2 * u ^ 2 ≤ 1
    linarith [h5]