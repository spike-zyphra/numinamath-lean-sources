import Mathlib

theorem algebra_6489 (x : Real) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.sin x = 4 / 5) :
    Real.tan x + (Real.cos x)^2 / 3 = 1 + 34 / 75 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h2 : (Real.cos x) ^ 2 = 9 / 25 := by
    have hcos : (Real.cos x) ^ 2 + (Real.sin x) ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h] at hcos
    nlinarith
  have htan : Real.tan x = 4 / 3 := by 
    rw [Real.tan_eq_sin_div_cos]
    have hcosx : Real.cos x = 3 / 5 := by
      nlinarith [Real.cos_sq_add_sin_sq x, h, h1]
    rw [hcosx, h]
    all_goals norm_num
  rw [htan]
  rw [h2]
  all_goals norm_num