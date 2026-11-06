import Mathlib

open Real Set
open scoped Real

theorem inequalities_297573 (x : Real) (hx : x ∈ Ioo 0 (π / 2)) (h : 2 * (sin x)^2 - 7 * abs (sin x) + 3 < 0) :
    30 * π / 180 < x ∧ x < 90 * π / 180 := by 
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 < x := hx1
  have h2 : x < π / 2 := hx2
  have h3 : 0 < sin x := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h4 : abs (sin x) = sin x := by 
    rw [abs_of_pos h3]
  rw [h4] at h 
  have h5 : sin x > 1 / 2 := by
    nlinarith [h, sq_nonneg (sin x - 1 / 2), sq_nonneg (sin x - 3)]
  have h6 : x > π / 6 := by
    by_contra h7
    push_neg at h7 
    have h8 : x ≤ π / 6 := by linarith 
    have h9 : sin x ≤ sin (π / 6) := by
      apply sin_le_sin_of_le_of_le_pi_div_two 
      all_goals 
        nlinarith [Real.pi_pos] 
    have h10 : sin (π / 6) = 1 / 2 := by 
      exact sin_pi_div_six 
    have h11 : sin x ≤ 1 / 2 := by 
      linarith [h9, h10] 
    linarith [h5, h11]
  have h7 : x < π / 2 := h2 
  constructor
  · -- Show that 30 * π / 180 < x
    have h8 : π / 6 < x := h6 
    have h9 : 30 * π / 180 = π / 6 := by 
      ring_nf
    linarith [h9, h8]
  · -- Show that x < 90 * π / 180
    have h10 : x < π / 2 := h2 
    have h11 : 90 * π / 180 = π / 2 := by 
      ring_nf
    linarith [h11, h10]