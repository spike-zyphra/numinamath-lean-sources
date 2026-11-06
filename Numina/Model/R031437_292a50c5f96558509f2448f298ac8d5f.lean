import Mathlib

open Real Set
open scoped Real

theorem inequalities_5704 (A B C : Real)
  (h : sin A + sin B + sin C ≥ 2) :
  cos A + cos B + cos C ≤ sqrt 5 := by
  have h1 : sin A ^ 2 + cos A ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq A
  have h2 : sin B ^ 2 + cos B ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq B
  have h3 : sin C ^ 2 + cos C ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq C
  have h4 : sin A ^ 2 + sin B ^ 2 + sin C ^ 2 + cos A ^ 2 + cos B ^ 2 + cos C ^ 2 = 3 := by
    have h5 : sin A ^ 2 + cos A ^ 2 = 1 := h1
    have h6 : sin B ^ 2 + cos B ^ 2 = 1 := h2
    have h7 : sin C ^ 2 + cos C ^ 2 = 1 := h3
    linarith
  have h5 : (sin A + sin B + sin C) ^ 2 ≤ 3 * (sin A ^ 2 + sin B ^ 2 + sin C ^ 2) := by
    linarith [sq_nonneg (sin A - sin B), sq_nonneg (sin B - sin C), sq_nonneg (sin C - sin A)]
  have h6 : sin A ^ 2 + sin B ^ 2 + sin C ^ 2 ≥ 4 / 3 := by
    nlinarith [h, h5]
  have h7 : cos A ^ 2 + cos B ^ 2 + cos C ^ 2 ≤ 5 / 3 := by
    nlinarith [h4, h6]
  have h8 : (cos A + cos B + cos C) ^ 2 ≤ 3 * (cos A ^ 2 + cos B ^ 2 + cos C ^ 2) := by
    linarith [sq_nonneg (cos A - cos B), sq_nonneg (cos B - cos C), sq_nonneg (cos C - cos A)]
  have h9 : (cos A + cos B + cos C) ^ 2 ≤ 5 := by
    nlinarith [h7, h8]
  have h10 : cos A + cos B + cos C ≤ Real.sqrt 5 := by
    have h11 : (cos A + cos B + cos C) ^ 2 ≤ 5 := h9
    have h12 : Real.sqrt (5 : ℝ) ≥ 0 := by positivity
    have h13 : (cos A + cos B + cos C : ℝ) ≤ Real.sqrt (5) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    exact h13
  exact h10