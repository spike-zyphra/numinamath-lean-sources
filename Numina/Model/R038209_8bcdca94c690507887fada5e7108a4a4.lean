import Mathlib

open Real Set
open scoped Real

theorem inequalities_221008 (x : ℝ) :
  (sin x)^5 + (cos x)^5 + (sin x)^4 ≤ 2 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h2 : sin x ^ 2 ≤ 1 := by 
    have hsin1 : -1 ≤ sin x := by
      apply neg_one_le_sin
    have hsin2 : sin x ≤ 1 := by
      apply sin_le_one
    nlinarith
  have h3 : cos x ^ 2 ≤ 1 := by 
    have hcos1 : -1 ≤ cos x := by
      apply neg_one_le_cos
    have hcos2 : cos x ≤ 1 := by
      apply cos_le_one
    nlinarith
  have h4 : sin x ^ 5 ≤ sin x ^ 2 := by
    have h7 : -1 ≤ sin x := by
      apply neg_one_le_sin
    have h8 : sin x ≤ 1 := by
      apply sin_le_one
    nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (sin x), sq_nonneg (sin x - 1), sq_nonneg (sin x + 1), sq_nonneg (sin x ^ 2), sq_nonneg (sin x ^ 2 - sin x)]
  have h5 : cos x ^ 5 ≤ cos x ^ 2 := by
    have h7 : -1 ≤ cos x := by
      apply neg_one_le_cos
    have h8 : cos x ≤ 1 := by
      apply cos_le_one
    nlinarith [sq_nonneg (cos x ^ 2 - 1), sq_nonneg (cos x), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (cos x ^ 2), sq_nonneg (cos x ^ 2 - cos x)]
  have h6 : sin x ^ 2 + cos x ^ 2 = 1 := h1
  have h7 : sin x ^ 5 + cos x ^ 5 ≤ 1 := by
    nlinarith [h4, h5, h6, sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x)]
  have h8 : sin x ^ 4 ≤ 1 := by
    have h11 : sin x ^ 2 ≤ 1 := h2
    nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (sin x ^ 2), sq_nonneg (sin x ^ 2 - 1)]
  linarith [h7, h8]