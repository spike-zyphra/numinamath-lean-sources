import Mathlib

theorem algebra_5773 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.tan x = 4 / 3) :
    5 * Real.cos x + 10 * Real.sin x = 11 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < Real.pi / 2 := hx.2

  have h1 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [hx1, hx2, Real.pi_pos]
    linarith [hx1, hx2, Real.pi_pos]

  have h2 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hx1, Real.pi_pos]
    linarith [hx2, Real.pi_pos]

  have h3 : Real.sin x = 4 / 3 * Real.cos x := by
    have h4 : Real.cos x ≠ 0 := by linarith [h1]
    rw [Real.tan_eq_sin_div_cos] at h
    field_simp at h ⊢
    nlinarith

  have h5 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  rw [h3] at h5
  have h6 : Real.cos x = 3 / 5 := by
    nlinarith [h5, h1]

  have h7 : Real.sin x = 4 / 5 := by
    rw [h6] at h3
    nlinarith

  rw [h6, h7]
  norm_num