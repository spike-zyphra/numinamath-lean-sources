import Mathlib

open Real Set
open scoped Real

theorem algebra_204938 {x y : ℝ} (hx : x ∈ Ioo 0 (π / 2)) (hy : y ∈ Ioo 0 (π / 2))
    (h : sin y = 2005 * cos (x + y) * sin x) :
    tan y ≤ (2005 * sqrt 2006) / 4012 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : sin y > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h2 : cos y > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h3 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h4 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h5 : cos (x + y) = cos x * cos y - sin x * sin y := by
    rw [cos_add]
  rw [h5] at h
  have h6 : sin y * (1 + 2005 * sin x ^ 2) = 2005 * cos x * sin x * cos y := by
    nlinarith [h, mul_pos h1 h3, mul_pos h1 h4, mul_pos h3 h4]
  have h7 : tan y = (2005 * cos x * sin x) / (1 + 2005 * sin x ^ 2) := by
    have h8 : cos y > 0 := h2
    have h9 : sin y > 0 := h1
    have h10 : sin y * (1 + 2005 * sin x ^ 2) = 2005 * cos x * sin x * cos y := h6
    have h11 : tan y = sin y / cos y := by
      rw [tan_eq_sin_div_cos]
    rw [h11]
    field_simp [h8, h9]
    nlinarith
  have h8 : tan y = (2005 * tan x) / (1 + 2006 * tan x ^ 2) := by
    have h9 : tan y = (2005 * cos x * sin x) / (1 + 2005 * sin x ^ 2) := h7
    have h10 : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [h9, h10]
    field_simp [show cos x ≠ 0 by linarith, show sin x > 0 by linarith]
    <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2), sq_nonneg (sin x * cos x)]
  have h11 : tan x > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith
    · linarith
  have h12 : tan y ≤ (2005 * sqrt 2006) / 4012 := by
    rw [h8]
    have h13 : tan x > 0 := h11
    have h14 : (1 + 2006 * tan x ^ 2) > 0 := by positivity
    have h15 : (2005 * tan x) / (1 + 2006 * tan x ^ 2) ≤ (2005 * sqrt 2006) / 4012 := by
      have h16 : (sqrt 2006) > 0 := by positivity
      have h17 : (sqrt 2006) ^ 2 = (2006 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have h18 : (2005 * tan x) / (1 + 2006 * tan x ^ 2) ≤ (2005 * sqrt 2006) / 4012 := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg ((sqrt 2006 * tan x) - 1), sq_nonneg (tan x ^ 2 - 1 / 2006), sq_nonneg (tan x * sqrt 2006 - 1), sq_nonneg (tan x ^ 2 - 1 / 2006), sq_nonneg (tan x * (sqrt 2006)), sq_nonneg (tan x - 1 / sqrt 2006), Real.sqrt_pos.mpr (by norm_num : (2006 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2006 : ℝ) by norm_num)]
      linarith
    exact h15
  exact h12