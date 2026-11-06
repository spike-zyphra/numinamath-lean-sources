import Mathlib

open Real Set
open scoped Real

theorem algebra_309146 {x y : ℝ} (hx : 0 < x) (hy : x < y)
  (hyy : y < π/2) (h : tan y = tan x + 1/cos x) :
  y - x/2 = π/4 := by
  have h1 : 0 < y := by linarith
  have h2 : cos x ≠ 0 := by
    have h3 : x < π/2 := by linarith [hyy, hy]
    have h4 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith
      linarith
    linarith
  have h5 : cos y ≠ 0 := by
    have h6 : y < π/2 := by linarith
    have h7 : cos y > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith
      linarith
    linarith
  have htan : tan y = sin y / cos y := by rw [tan_eq_sin_div_cos]
  have htanx : tan x = sin x / cos x := by rw [tan_eq_sin_div_cos]
  rw [htan, htanx] at h
  have h_eq1 : sin y * cos x = cos y * (sin x + 1) := by 
    have h8 : cos x ≠ 0 := h2
    have h9 : cos y ≠ 0 := h5
    field_simp [h8, h9] at h ⊢
    linarith
  have h_eq2 : sin (y - x) = cos y := by
    have h_eq3 : sin y * cos x - cos y * sin x = cos y := by
      linarith [h_eq1]
    have h_eq4 : sin (y - x) = sin y * cos x - cos y * sin x := by 
      rw [sin_sub]
      <;> ring
    rw [h_eq4]
    linarith
  have h8 : sin (y - x) = sin (Real.pi / 2 - y) := by
    have h9 : sin (Real.pi / 2 - y) = cos y := by 
      rw [sin_pi_div_two_sub]
    rw [h9] at *
    linarith [h_eq2]
  have h9 : y - x < Real.pi / 2 := by 
    have h10 : y < Real.pi / 2 := by linarith
    nlinarith [show 0 < x by linarith, h10]
  have h11 : 0 < Real.pi / 2 - y := by
    linarith [show y < Real.pi / 2 by linarith]
  have h12 : y - x = Real.pi / 2 - y := by
    have h13 : sin (y - x) = sin (Real.pi / 2 - y) := h8
    have h21 : Real.pi / 2 - y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have h22 : y - x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · nlinarith [Real.pi_pos, show y < Real.pi / 2 by linarith]
      · nlinarith [Real.pi_pos, show y < Real.pi / 2 by linarith, show 0 < x by linarith]
    apply Real.injOn_sin h22 h21 h13
  linarith [h12]