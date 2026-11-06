import Mathlib

open Real Set
open scoped Real

theorem algebra_326230 (x y : ℝ) (h : sin x + sin y = 1) :
    cos x + cos y ∈ Icc (-sqrt 3) (sqrt 3) := by
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h3 : sin y ^ 2 + cos y ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq y
  have h4 : (sin x + sin y)^2 = 1 := by
    rw [h]
    norm_num
  have h6 : (cos x + cos y) ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg (cos x - cos y), sq_nonneg (sin x - sin y),
          Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y,
          sq_nonneg (x - y), sq_nonneg (sin x * sin y - cos x * cos y),
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h7 : cos x + cos y ≤ sqrt 3 := by
    have h7 : (cos x + cos y) ^ 2 ≤ (3 : ℝ) := by linarith
    have h8 : cos x + cos y ≤ Real.sqrt 3 := by
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have h9 : -Real.sqrt 3 ≤ cos x + cos y := by
    have h7 : (cos x + cos y) ^ 2 ≤ (3 : ℝ) := by linarith
    have h8 : -Real.sqrt 3 ≤ cos x + cos y := by
      have h9 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h7]
    linarith
  constructor
  · linarith [h9]
  · linarith [h7]
  all_goals linarith
  all_goals nlinarith [Real.sqrt_nonneg 3]
  all_goals nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y]