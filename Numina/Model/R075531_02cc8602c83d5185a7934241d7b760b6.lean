import Mathlib

theorem algebra_6184 (x : ℝ) (hx : Real.cos x = 5 / 13) (hxp : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 + Real.sin x ^ 2 / Real.tan x ^ 2 - Real.sin x ^ 2 = 50 / 169 := by
  have h1 : 0 < x := hxp.left
  have h2 : x < Real.pi / 2 := hxp.right
  have h3 : 0 < Real.sin x := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h4 : Real.sin x ^ 2 = 144 / 169 := by 
    have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [hx] at h5
    nlinarith
  have h6 : Real.sin x = 12 / 13 := by 
    nlinarith [h3]
  have htan : Real.tan x = 12 / 5 := by 
    have htan_def : Real.tan x = Real.sin x / Real.cos x := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan_def, h6, hx]
    all_goals norm_num
  have htan2 : Real.tan x ^ 2 = 144 / 25 := by 
    rw [htan]
    norm_num
  have hsin2 : Real.sin x ^ 2 = 144 / 169 := h4
  rw [hsin2, htan2]
  <;> field_simp
  <;> norm_num
  <;> linarith