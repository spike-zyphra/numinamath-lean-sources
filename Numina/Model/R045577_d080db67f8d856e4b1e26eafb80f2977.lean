import Mathlib

open Real Set
open scoped Real

theorem algebra_178760 (α : ℝ) (h₀ : sin (α - π / 2) = -2 / 3) (h₁ : 270 * π / 180 < α ∧ α < 360 * π / 180) :
    1 / tan (2 * α) = sqrt 5 / 20 := by

  have h2 : cos α = 2 / 3 := by
    have h3 : sin (α - π / 2) = -cos α := by
      rw [sin_sub, sin_pi_div_two, cos_pi_div_two]
      ring
    rw [h3] at h₀
    linarith

  have h4 : sin α < 0 := by
    have h5 : 270 * π / 180 < α := h₁.1
    have h6 : α < 360 * π / 180 := h₁.2
    have h7 : 3 * π / 2 < α := by
      nlinarith [h₁.1, Real.pi_pos]
    have h8 : α < 2 * π := by
      nlinarith [h₁.2, Real.pi_pos]
    have h9 : sin α = -sin (2 * π - α) := by
      rw [show 2 * π - α = 2 * π - α by rfl]
      rw [sin_sub, sin_two_pi, cos_two_pi]
      ring
    have h10 : 0 < 2 * π - α := by
      nlinarith [h₁.2, Real.pi_pos]
    have h11 : sin (2 * π - α) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h₁.2, Real.pi_pos]
      linarith [h₁.2, Real.pi_pos]
    linarith [h9, h11]

  have h8 : sin α ^ 2 = 5 / 9 := by
    have h9 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [h2] at h9
    nlinarith

  have h10 : sin α = -Real.sqrt 5 / 3 := by
    have h11 : sin α < 0 := h4
    have h12 : sin α ^ 2 = 5 / 9 := h8
    have h13 : Real.sqrt 5 ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      all_goals linarith
    have h14 : sin α = -Real.sqrt 5 / 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (5: ℝ) by norm_num), Real.sqrt_nonneg 5]
    exact h14

  have h15 : cos (2 * α) = -1 / 9 := by
    have h16 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h16, h2]
    norm_num

  have h17 : sin (2 * α) = -4 * Real.sqrt 5 / 9 := by
    have h18 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
    rw [h18, h10, h2]
    ring_nf

  have h18 : tan (2 * α) = 4 * Real.sqrt 5 := by
    rw [tan_eq_sin_div_cos, h17, h15]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  rw [h18]
  field_simp
  <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]