import Mathlib

open Real Set
open scoped Real

theorem algebra_13581 {x : Real} (hx : x ∈ Ioo 0 (π / 2)) (hcos : cos x = 24 / 25) :
    (sin x - tan x) * (1 / sin x ^ 2) = -25 / 168 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have h2 : sin x = 7 / 25 := by
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [hcos] at h3
    have h4 : sin x ^ 2 = 49 / 625 := by
      nlinarith [h3, h1]
    have h5 : sin x = 7 / 25 := by
      nlinarith [h4, h1]
    linarith
  have htan : tan x = 7 / 24 := by
    rw [Real.tan_eq_sin_div_cos, h2, hcos]
    norm_num
  rw [htan, h2]
  have h6 : sin x ^ 2 = (7 / 25) ^ 2 := by
    rw [h2]
  field_simp [h1, hcos]
  <;> nlinarith