import Mathlib

theorem algebra_22351 (x : ℝ) (h : ∃ r ≠ 0 ,Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 ∧  Real.tan x ≠ 0 ∧  Real.cos x = r * Real.sin x ∧ Real.tan x = r * Real.cos x) :
    Real.cos x ^ 3 + Real.cos x ^ 2 = 1 := by

  rcases h with ⟨r, hr1, h1, h2, h3, h4, h5⟩

  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at h5

  have hr : r = Real.cos x / Real.sin x := by
    have h6 : Real.sin x ≠ 0 := h1
    have h7 : Real.cos x = r * Real.sin x := h4
    field_simp [h6] at *
    nlinarith

  rw [hr] at h5

  have h8 : Real.sin x ^ 2 = Real.cos x ^ 3 := by
    have h6 : Real.sin x ≠ 0 := h1
    have h7 : Real.cos x ≠ 0 := h2
    field_simp [h7, h6] at h5 ⊢
    nlinarith [sq_pos_of_ne_zero h6, sq_pos_of_ne_zero h7, Real.sin_sq_add_cos_sq x]

  have h9 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  nlinarith [h8, h9]