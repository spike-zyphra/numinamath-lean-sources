import Mathlib

open Real Set
open scoped Real

theorem calculus_22112 (x : ℝ) (hcos_ne_zero : cos x ≠ 0) (_ : sin x ≠ 0)
    (h : 1 / cos x + tan x = 22 / 7) :
    1 / sin x + cot x = 29 / 15 := by
  have htan_x : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [htan_x] at h
  have h1 : 1 + sin x = 22 / 7 * cos x := by
    field_simp [hcos_ne_zero] at h ⊢
    linarith
  have h2 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have h3 : cos x = 7 / 22 * (1 + sin x) := by
    linarith
  rw [h3] at h2
  have h4 : 533 * sin x ^ 2 + 98 * sin x - 435 = 0 := by
    ring_nf at h2 ⊢
    nlinarith
  have h5 : sin x = 435 / 533 ∨ sin x = -1 := by
    have h6 : 533 * sin x ^ 2 + 98 * sin x - 435 = 0 := h4
    have : (sin x - 435 / 533) * (sin x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp this) with h7 h8
    · left
      linarith
    · right
      linarith
  cases h5 with
  | inl h5 =>
    have h6 : sin x = 435 / 533 := h5
    have h7 : cos x = 308 / 533 := by
      rw [h6] at h3
      linarith
    have htan_x2 : cot x = cos x / sin x := by
      rw [cot_eq_cos_div_sin]
    rw [htan_x2]
    rw [h6, h7]
    field_simp [show sin x ≠ 0 by assumption]
    <;> norm_num
  | inr h5 =>
    have h6 : sin x = -1 := h5
    have h7 : cos x = 0 := by
      rw [h6] at h3
      linarith
    exfalso
    exact hcos_ne_zero h7