import Mathlib

theorem algebra_5848 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.tan x = 15 / 17) :
    (Real.cos x - Real.sin x) / (Real.cos x + Real.sin x) = 1 / 16 := by 
  have h1 : Real.cos x ≠ 0 := by
    have hx1 : 0 < x := hx.1
    have hx2 : x < Real.pi / 2 := hx.2
    have hcos : Real.cos x > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, hx1, hx2]
      · linarith [Real.pi_pos, hx1, hx2]
    positivity
  have h2 : Real.sin x > 0 := by
    have hx1 : 0 < x := hx.1
    have hx2 : x < Real.pi / 2 := hx.2
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith
    linarith [Real.pi_pos]
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at h
  have h3 : Real.sin x = 15 / 17 * Real.cos x := by
    have h6 : Real.cos x > 0 := by
      have hx1 : 0 < x := hx.1
      have hx2 : x < Real.pi / 2 := hx.2
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, hx1, hx2]
      · linarith [Real.pi_pos, hx1, hx2]
    field_simp [h6] at h
    nlinarith
  have h4 : Real.cos x - Real.sin x = 2 / 17 * Real.cos x := by 
    rw [h3]
    ring
  have h5 : Real.cos x + Real.sin x = 32 / 17 * Real.cos x := by 
    rw [h3]
    ring
  have h6 : Real.cos x > 0 := by
    have hx1 : 0 < x := hx.1
    have hx2 : x < Real.pi / 2 := hx.2
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, hx1, hx2]
    · linarith [Real.pi_pos, hx1, hx2]
  rw [h4, h5]
  have hcosn : Real.cos x ≠ 0 := by
    linarith
  field_simp [h6]
  <;> nlinarith