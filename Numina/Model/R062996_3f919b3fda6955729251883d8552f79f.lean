import Mathlib
open Real Set
open scoped Real

theorem algebra_5556 (x : ℝ) (hx : x ∈ Ioo 0 (π / 2)) (h : sin x = 5 / 13) :
    (1 - tan x) / cos x = 91 / 144 := by
  have hx1 : 0 < x := hx.left
  have hx2 : x < π / 2 := hx.right
  -- Show that cos x > 0 in the first quadrant
  have hx3 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith [Real.pi_pos]
  -- Calculate cos x using the Pythagorean identity
  have hcos : cos x = 12 / 13 := by
    have h1 : cos x ^ 2 = 1 - sin x ^ 2 := by
      rw [←Real.cos_sq_add_sin_sq x]
      linarith
    rw [h] at h1
    have h2 : cos x ^ 2 = 144 / 169 := by
      nlinarith
    have h3 : cos x = 12 / 13 := by
      nlinarith [sq_pos_of_pos hx3]
    exact h3
  -- Calculate tan x from sin x and cos x
  have htan : tan x = 5 / 12 := by
    rw [tan_eq_sin_div_cos, h, hcos]
    all_goals norm_num
  -- Calculate (1 - tan x) / cos x
  rw [htan, hcos]
  all_goals norm_num