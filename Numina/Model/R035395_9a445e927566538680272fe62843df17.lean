import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9277 (f : ℝ → ℝ) (hf : f = tan) (x : ℝ) (hx : x ∈ Icc 0 (π/4)) :
  f x ∈ Icc 0 1 := by
  rcases hx with ⟨hx0, hx1⟩
  rw [hf]
  have h1 : 0 ≤ x := by linarith
  have h2 : x ≤ π / 4 := by linarith
  have htan1 : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [pi_pos]
    linarith [pi_pos]
  have htan2 : 0 < cos x := by
    have h1 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [pi_pos]
      · linarith [pi_pos]
    linarith
  have htan3 : 0 ≤ tan x := by
    rw [Real.tan_eq_sin_div_cos]
    apply div_nonneg
    linarith [htan1]
    linarith [htan2]
  have htan4 : tan x ≤ 1 := by
    rw [Real.tan_eq_sin_div_cos]
    have h6 : sin x ≤ cos x := by
      have h7 : x ≤ π / 4 := by linarith
      have h8 : sin x ≤ sin (π / 4) := by 
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals linarith [pi_pos]
      have h9 : cos x ≥ cos (π / 4) := by 
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        all_goals linarith [pi_pos]
      have h10 : cos (π / 4) = sin (π / 4) := by
        have h1 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        have h2 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        linarith [h1, h2]
      have h11 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h8 : cos x > 0 := htan2
    have h18 : sin x / cos x ≤ (cos x) / cos x := by 
      apply (div_le_div_right h8).mpr
      linarith [h6]
    have h19 : (cos x) / cos x = 1 := by 
      field_simp [h8]
    linarith [h18, h19]
  constructor
  · linarith [htan3]
  · linarith [htan4]