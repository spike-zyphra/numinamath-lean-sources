import Mathlib

open Real Set
open scoped Real

theorem inequalities_307732 (x : ℝ) :
  (sin x)^10 + (cos x)^10 ≥ 1/16 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h4 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := by
    linarith
  have h5 : (sin x) ^ 10 + (cos x) ^ 10 = ((sin x) ^ 2) ^ 5 + ((cos x) ^ 2) ^ 5 := by ring
  rw [h5]
  have h6 : ((sin x) ^ 2) ^ 5 + ((cos x) ^ 2) ^ 5 ≥ 1 / 16 := by
    have h7 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := h4
    have h8 : (cos x) ^ 2 = 1 - (sin x) ^ 2 := by
      linarith
    rw [h8]
    nlinarith [sq_nonneg ((sin x) ^ 2 - 1 / 2), sq_nonneg ((sin x) ^ 2 - (1 - (sin x) ^ 2)), 
      sq_nonneg ((sin x) ^ 2 - 1 / 2), sq_nonneg ((sin x) ^ 2 - 0), sq_nonneg ((sin x) ^ 2 - 1), 
      sq_nonneg ((sin x) ^ 2 ^ 2 - 1 / 4), sq_nonneg ((sin x) ^ 2 * ((sin x) ^ 2 - 1 / 2)), 
      sq_nonneg ((sin x) ^ 2 ^ 2 - ((sin x) ^ 2) / 4), 
      sq_nonneg (((sin x) ^ 2) ^ 2 - (1 - (sin x) ^ 2) ^ 2)
    ]
  linarith