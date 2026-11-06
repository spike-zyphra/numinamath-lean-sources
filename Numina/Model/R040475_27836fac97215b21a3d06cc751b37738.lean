import Mathlib

open Real Set
open scoped Real

theorem calculus_22680 (x : ℝ) (hx : x ∈ Ioo π (3 * π / 2)) (hcos : cos x = -20 / 29) :
    tan x = 21 / 20 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x < 0 := by
    have h6 : π < x := hx1
    have h7 : x < 3 * π / 2 := hx2
    have h8 : x - π > 0 := by linarith
    have h9 : x - π < π / 2 := by
      nlinarith [pi_pos]
    have h10 : sin x = -sin (x - π) := by 
      rw [show x = π + (x - π) by ring]
      rw [sin_add]
      simp [sin_pi, cos_pi]
      all_goals nlinarith [pi_pos]
    have h11 : sin (x - π) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [pi_pos]
    nlinarith
  have h2 : sin x ^ 2 = 441 / 841 := by
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    rw [hcos] at h3
    nlinarith
  have h3 : sin x = -21 / 29 := by
    nlinarith
  rw [tan_eq_sin_div_cos]
  rw [h3, hcos]
  all_goals norm_num