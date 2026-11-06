import Mathlib

open Real Set
open scoped Real

theorem inequalities_174130 (x y : ℝ) :
  cos (x + y) * cos (x - y) ≤ (cos x) ^ 2 := by
  have h1 : cos (x + y) = cos x * cos y - sin x * sin y := by
    rw [cos_add]
  have h2 : cos (x - y) = cos x * cos y + sin x * sin y := by
    rw [cos_sub]
  rw [h1, h2]
  have h3 : (cos x * cos y - sin x * sin y) * (cos x * cos y + sin x * sin y) =
    (cos x ^ 2) * (cos y ^ 2) - (sin x ^ 2) * (sin y ^ 2) := by
    ring
  have h4 : (cos x ^ 2) + (sin x ^ 2) = 1 := by
    exact Real.cos_sq_add_sin_sq x
  have h5 : (cos y ^ 2) + (sin y ^ 2) = 1 := by
    exact Real.cos_sq_add_sin_sq y
  have h6 : (sin y) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h7 : (cos x) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h8 : (sin x) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h9 : (cos y) ^ 2 ≥ 0 := by
    apply sq_nonneg
  nlinarith [sq_nonneg (cos x * sin y), sq_nonneg (sin x * sin y - cos x * cos y), sq_nonneg (sin x * sin y + cos x * cos y), sq_nonneg (sin y), sq_nonneg (cos x), sq_nonneg (sin x), sq_nonneg (cos y), sq_nonneg (sin x * sin y), sq_nonneg (cos x * cos y), sq_nonneg (cos x * sin y - sin x * sin y), sq_nonneg (cos x * sin y + sin x * sin y)]