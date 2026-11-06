import Mathlib

open Real Set
open scoped Real

theorem algebra_154211 (f : ℝ → ℝ)
  (h₀ : ∀ x, 0 < x ∧ x < π / 2 → f x = tan x + 1 / tan x + 1 / sin x - 1 / cos x) :
  ∀ x, 0 < x ∧ x < π / 2 → 1 < f x := by 
  intro x h 
  have h1 : 0 < x := h.1
  have h2 : x < π / 2 := h.2
  have hx3 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, Real.pi_pos]
    linarith [h2, Real.pi_pos]
  have hx4 : cos x > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h1, h2, Real.pi_pos]
  have hx5 : sin x < 1 := by
    have h3 : sin x < sin (π / 2 : ℝ) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [h1, h2, Real.pi_pos]
    have h4 : sin (π / 2 : ℝ) = 1 := by
      rw [sin_pi_div_two]
    linarith [h3, h4]
  have hx6 : 1 - sin x > 0 := by 
    linarith [hx5]
  have hx7 : 1 + cos x > 1 := by 
    have h8 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    linarith
  have hx8 : (1 - sin x) * (1 + cos x) > 0 := by
    positivity
  have hfx : f x = tan x + 1 / tan x + 1 / sin x - 1 / cos x := by 
    apply h₀ x h
  rw [hfx]
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  have h17 : tan x + 1 / tan x = 1 / (sin x * cos x) := by
    rw [htan]
    have h18 : cos x ≠ 0 := by 
      linarith [hx4]
    have h19 : sin x ≠ 0 := by
      linarith [hx3]
    field_simp [h18, h19]
    <;> nlinarith [Real.sin_sq_add_cos_sq x]
  have h50 : sin x * cos x > 0 := by 
    apply mul_pos 
    all_goals linarith [hx3, hx4]
  have hx14 : (tan x + 1 / tan x + 1 / sin x - 1 / cos x - 1) > 0 := by 
    rw [show tan x + 1 / tan x = 1 / (sin x * cos x) by linarith [h17]]
    have h51 : 1 / (sin x * cos x) + 1 / sin x - 1 / cos x - 1 > 0 := by
      have h22 : sin x * cos x ≠ 0 := by 
        apply mul_ne_zero
        all_goals 
          try linarith [hx3]
          try linarith [hx4]
      have h24 : 1 / (sin x * cos x) + 1 / sin x - 1 / cos x - 1 = (1 + cos x - sin x - sin x * cos x) / (sin x * cos x) := by 
        field_simp [h22, hx3, hx4]
        <;> ring_nf <;> 
          nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2)]
      rw [h24]
      apply div_pos 
      · -- Show the numerator is positive 
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x - cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, mul_pos hx3 hx4, hx6, hx8]
      all_goals -- Show the denominator is positive
        positivity 
    linarith 
  linarith [hx14]
  all_goals linarith