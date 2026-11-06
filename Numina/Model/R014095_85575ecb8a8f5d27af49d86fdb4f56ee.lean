import Mathlib

open Real Set
open scoped Real

theorem inequalities_4834 (a b c d e : ℝ)
  (h : sin a + sin b + sin c + sin d + sin e ≥ 3) :
  cos a + cos b + cos c + cos d + cos e ≤ 4 := by 
  have h1 : sin a ^ 2 + cos a ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq a
  have h2 : sin b ^ 2 + cos b ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq b
  have h3 : sin c ^ 2 + cos c ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq c
  have h4 : sin d ^ 2 + cos d ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq d
  have h5 : sin e ^ 2 + cos e ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq e
  have h6 : sin a ^ 2 + sin b ^ 2 + sin c ^ 2 + sin d ^ 2 + sin e ^ 2 = 5 - (cos a ^ 2 + cos b ^ 2 + cos c ^ 2 + cos d ^ 2 + cos e ^ 2) := by
    linarith
  have h7 : (sin a + sin b + sin c + sin d + sin e) ^ 2 ≤ 5 * (sin a ^ 2 + sin b ^ 2 + sin c ^ 2 + sin d ^ 2 + sin e ^ 2) := by
    nlinarith [sq_nonneg (sin a - sin b), sq_nonneg (sin a - sin c), sq_nonneg (sin a - sin d), sq_nonneg (sin a - sin e),
      sq_nonneg (sin b - sin c), sq_nonneg (sin b - sin d), sq_nonneg (sin b - sin e),
      sq_nonneg (sin c - sin d), sq_nonneg (sin c - sin e), sq_nonneg (sin d - sin e)]
  have h8 : (cos a + cos b + cos c + cos d + cos e) ^ 2 ≤ 5 * (cos a ^ 2 + cos b ^ 2 + cos c ^ 2 + cos d ^ 2 + cos e ^ 2) := by
    nlinarith [sq_nonneg (cos a - cos b), sq_nonneg (cos a - cos c), sq_nonneg (cos a - cos d), sq_nonneg (cos a - cos e),
      sq_nonneg (cos b - cos c), sq_nonneg (cos b - cos d), sq_nonneg (cos b - cos e),
      sq_nonneg (cos c - cos d), sq_nonneg (cos c - cos e), sq_nonneg (cos d - cos e)]
  have h9 : sin a ^ 2 + sin b ^ 2 + sin c ^ 2 + sin d ^ 2 + sin e ^ 2 + (cos a ^ 2 + cos b ^ 2 + cos c ^ 2 + cos d ^ 2 + cos e ^ 2) = 5 := by
    linarith [h1, h2, h3, h4, h5]
  have h10 : (cos a + cos b + cos c + cos d + cos e) ^ 2 ≤ 16 := by
    nlinarith [sq_nonneg ((sin a) + (sin b) + (sin c) + (sin d) + (sin e) - 3), sq_nonneg ((cos a) + (cos b) + (cos c) + (cos d) + (cos e)), 
      h7, h8, h9, h
    ]
  have h11 : cos a + cos b + cos c + cos d + cos e ≤ 4 := by 
    nlinarith [h10, sq_nonneg ((cos a + cos b + cos c + cos d + cos e) - 4), sq_nonneg ((sin a + sin b + sin c + sin d + sin e) - 3)]
  exact h11