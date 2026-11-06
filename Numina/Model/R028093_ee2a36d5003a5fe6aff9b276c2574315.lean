import Mathlib

open Real Set
open scoped Real

theorem algebra_141185 {x : ℝ} (hx : 0 < x ∧ x < π/2) (h : sin x ^ 4 / 9 + cos x ^ 4 / 4 = 1/13) :
    tan x = 3/2 := by 
  have hx1 : 0 < x := hx.1
  have hx2 : x < π / 2 := hx.2
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hx1, Real.pi_pos]
    linarith [hx1, Real.pi_pos, hx2]
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [hx1, Real.pi_pos, hx2]
    linarith [hx1, Real.pi_pos, hx2]
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h5 : sin x ^ 2 = 9 / 13 := by
    nlinarith [sq_nonneg (sin x ^ 2 - 9 / 13), sq_nonneg (cos x ^ 2 - 4 / 13), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, mul_pos h1 h2]
  have h6 : cos x ^ 2 = 4 / 13 := by
    nlinarith [h3, h5]
  have h7 : sin x = 3 / Real.sqrt 13 := by
    have h8 : sin x ^ 2 = 9 / 13 := h5
    have h9 : sin x > 0 := h1
    have h10 : sin x = Real.sqrt (9 / 13) := by
      rw [←h8]
      field_simp [h9]
    have h11 : Real.sqrt (9 / 13) = 3 / Real.sqrt 13 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h10, h11]
  have h8 : cos x = 2 / Real.sqrt 13 := by
    have h9 : cos x ^ 2 = 4 / 13 := h6
    have h10 : cos x > 0 := h2
    have h11 : cos x = Real.sqrt (4 / 13) := by
      rw [←h9]
      field_simp [h10]
    have h12 : Real.sqrt (4 / 13) = 2 / Real.sqrt 13 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h11, h12]
  have h9 : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [h9, h7, h8]
  field_simp
  <;> ring_nf <;> norm_num