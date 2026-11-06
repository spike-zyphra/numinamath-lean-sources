import Mathlib

open Real Set
open scoped Real

theorem inequalities_65181 (x : ℝ) (hx : 0 < x ∧ x < π/2) :
    cos x ^ 2 / tan x + sin x ^ 2 * tan x ≥ 1 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < π / 2 := hx.2
  have h1 : 0 < sin x := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]

  have h3 : cos x ^ 2 / tan x + sin x ^ 2 * tan x - 1 ≥ 0 := by
    rw [htan]
    have h6 : 0 < sin x * cos x := mul_pos h1 h2
    have h4 : 0 < sin x := h1
    have h5 : 0 < cos x := h2
    have h6' : cos x ^ 2 / (sin x / cos x) + sin x ^ 2 * (sin x / cos x) - 1 =
        (cos x ^ 3 / sin x) + (sin x ^ 3 / cos x) - 1 := by
      field_simp [h1.ne.symm, h2.ne.symm]
      <;> ring
    rw [h6']
    have h7 : (cos x ^ 3 / sin x) + (sin x ^ 3 / cos x) - 1 =
        (cos x ^ 4 + sin x ^ 4 - sin x * cos x) / (sin x * cos x) := by
      field_simp [h1.ne.symm, h2.ne.symm]
      ring
    rw [h7]
    have h8 : cos x ^ 4 + sin x ^ 4 - sin x * cos x ≥ 0 := by
      nlinarith [sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg (cos x - sin x), sq_nonneg (cos x), sq_nonneg (sin x), Real.sin_sq_add_cos_sq x, mul_pos h1 h2]
    have h9 : sin x * cos x > 0 := by
      apply mul_pos
      all_goals nlinarith
    have h10 : (cos x ^ 4 + sin x ^ 4 - sin x * cos x) / (sin x * cos x) ≥ 0 := by
      apply div_nonneg
      linarith [h8]
      all_goals nlinarith [h9]
    linarith [h10]
  linarith [h3]