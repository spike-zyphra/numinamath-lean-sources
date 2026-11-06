import Mathlib

open Real

theorem algebra_6437 (x : ℝ) (hx : x ∈ Set.Ioo 0 (π / 2)) (h : sin x = 5 / 13) :
    2 / cos x - tan x ^ 2 = 287 / 144 := by
  have h1 : 0 < x := hx.left
  have h2 : x < π / 2 := hx.right
  have hcos_pos : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, h2, Real.pi_pos]
    · linarith [h1, h2, Real.pi_pos]

  have hsin : sin x = 5 / 13 := h
  have hcos_sq : cos x ^ 2 = 1 - sin x ^ 2 := by
    have h : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    linarith 
  have hcos_sq' : cos x ^ 2 = 144 / 169 := by 
    rw [hsin] at hcos_sq 
    norm_num at hcos_sq ⊢
    exact hcos_sq
  have hcos : cos x = 12 / 13 := by
    nlinarith [hcos_sq', hcos_pos]
  
  have htan : tan x = 5 / 12 := by 
    have htan_eq_sin_div_cos : tan x = sin x / cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan_eq_sin_div_cos, hsin, hcos]
    all_goals norm_num

  have H1 : 2 / cos x = 13 / 6 := by 
    rw [hcos]
    field_simp
    <;> norm_num
  have H2 : tan x ^ 2 = 25 / 144 := by 
    rw [htan]
    norm_num 
  rw [H1, H2]
  all_goals norm_num