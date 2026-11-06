import Mathlib

open Real Set
open scoped Real

theorem algebra_318068 {x : ℝ} (hx : 0 < x ∧ x < π / 2)
  (h : sin x ^ 4 / 9 + cos x ^ 4 / 4 = 1 / 13) :
  tan x = 3 / 2 := by
  have h1 : 0 < x := hx.1
  have h2 : x < π / 2 := hx.2
  have h3 : 0 < sin x := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h4 : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have h5 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h_eq1 : sin x ^ 2 = 9 / 13 := by
    nlinarith [sq_nonneg (sin x ^ 2 - 9 / 13), sq_nonneg (cos x ^ 2 - 4 / 13), 
      Real.sin_sq_add_cos_sq x, 
      mul_pos h3 h4
      ]
  have h_eq2 : cos x ^ 2 = 4 / 13 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h_eq1]
  rw [tan_eq_sin_div_cos]
  have h_eq3 : sin x = 3 / Real.sqrt 13 := by
    have h_eq6 : sin x ^ 2 = 9 / 13 := h_eq1
    have h_eq3 : sin x > 0 := h3
    have h_eq5 : sin x = Real.sqrt (9 / 13) := by
      rw [← h_eq6]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg (9 / 13), Real.sqrt_nonneg (9 / 13)]
      <;> nlinarith [Real.sqrt_nonneg (9 / 13), Real.sqrt_nonneg (9 / 13)]
    have h_eq7 : Real.sqrt (9 / 13) = 3 / Real.sqrt 13 := by
      have h_eq8 : Real.sqrt (9 / 13) = Real.sqrt 9 / Real.sqrt 13 := by
        field_simp [Real.sqrt_div]
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h_eq8]
      have h_eq9 : Real.sqrt 9 = 3 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h_eq9]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring_nf <;> norm_num
    rw [h_eq7] at h_eq5
    linarith
  have h_eq4 : cos x = 2 / Real.sqrt 13 := by
    have h_eq3 : cos x ^ 2 = 4 / 13 := h_eq2
    have h_eq4 : cos x > 0 := h4
    have h_eq5 : cos x = Real.sqrt (4 / 13) := by
      rw [← h_eq3]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg (4 / 13), Real.sqrt_nonneg (4 / 13)]
      <;> nlinarith [Real.sqrt_nonneg (4 / 13), Real.sqrt_nonneg (4 / 13)]
    have h_eq7 : Real.sqrt (4 / 13) = 2 / Real.sqrt 13 := by
      have h_eq8 : Real.sqrt (4 / 13) = Real.sqrt 4 / Real.sqrt 13 := by
        field_simp [Real.sqrt_div]
        <;> ring_nf <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h_eq8]
      have h_eq9 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h_eq9]
      <;> ring_nf <;> norm_num
      <;> field_simp
      <;> ring_nf <;> norm_num
    rw [h_eq7] at h_eq5
    linarith
  rw [h_eq3, h_eq4]
  <;> field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num