import Mathlib

theorem algebra_13682 (x : Real) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.sin x = 24 / 25) :
    (1 / Real.cos x - Real.tan x) * Real.cos x ^ 2 = 7 / 625 := by
  have h1 : 0 < x := hx.1
  have h2 : x < Real.pi / 2 := hx.2
  have hcos_pos : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith [Real.pi_pos]
  have hcos_sq : Real.cos x ^ 2 = 49 / 625 := by
    have h3 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h] at h3
    nlinarith
  have hcos : Real.cos x = 7 / 25 := by
    nlinarith
  have htan : Real.tan x = 24 / 7 := by
    rw [Real.tan_eq_sin_div_cos, h, hcos]
    norm_num
  rw [htan, hcos_sq, hcos]
  field_simp
  <;> norm_num