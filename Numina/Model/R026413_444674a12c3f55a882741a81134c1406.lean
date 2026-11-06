import Mathlib

open Real
open scoped Real

theorem algebra_179037 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  tan (A / 2) * tan (B / 2) + tan (B / 2) * tan (C / 2) +
  tan (C / 2) * tan (A / 2) = 1 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : A / 2 + B / 2 + C / 2 = π / 2 := by
    linarith
  have h3 : cos (A / 2) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h3b : cos (B / 2) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h3c : cos (C / 2) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith
    · linarith
  have h4 : sin (A / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h4b : sin (B / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h4c : sin (C / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h9 : tan (A / 2) * tan (B / 2) + tan (B / 2) * tan (C / 2) + tan (C / 2) * tan (A / 2) =
      (sin (A / 2) * sin (B / 2) * cos (C / 2) + sin (B / 2) * sin (C / 2) * cos (A / 2) + sin (C / 2) * sin (A / 2) * cos (B / 2)) / (cos (A / 2) * cos (B / 2) * cos (C / 2)) := by
    have h9a : cos (A / 2) ≠ 0 := by nlinarith
    have h9b : cos (B / 2) ≠ 0 := by nlinarith
    have h9c : cos (C / 2) ≠ 0 := by nlinarith
    have h9d : tan (A / 2) = sin (A / 2) / cos (A / 2) := by rw [tan_eq_sin_div_cos]
    have h9e : tan (B / 2) = sin (B / 2) / cos (B / 2) := by rw [tan_eq_sin_div_cos]
    have h9f : tan (C / 2) = sin (C / 2) / cos (C / 2) := by rw [tan_eq_sin_div_cos]
    rw [h9d, h9e, h9f]
    field_simp [show cos (A / 2) ≠ 0 by nlinarith, show cos (B / 2) ≠ 0 by nlinarith, show cos (C / 2) ≠ 0 by nlinarith]
    ring
  rw [h9]
  have h9 : (sin (A / 2) * sin (B / 2) * cos (C / 2) + sin (B / 2) * sin (C / 2) * cos (A / 2) + sin (C / 2) * sin (A / 2) * cos (B / 2)) = cos (A / 2) * cos (B / 2) * cos (C / 2) := by
    have h14 : C / 2 = π / 2 - (A / 2 + B / 2) := by
      linarith
    have h15 : sin (C / 2) = cos (A / 2 + B / 2) := by
      rw [h14]
      have : sin (π / 2 - (A / 2 + B / 2)) = cos (A / 2 + B / 2) := by
        rw [sin_pi_div_two_sub]
      linarith
    have h16 : cos (C / 2) = sin (A / 2 + B / 2) := by
      rw [h14]
      have : cos (π / 2 - (A / 2 + B / 2)) = sin (A / 2 + B / 2) := by
        rw [cos_pi_div_two_sub]
      linarith
    rw [h15, h16]
    have h17 : sin (A / 2 + B / 2) = sin (A / 2) * cos (B / 2) + cos (A / 2) * sin (B / 2) := by
      rw [sin_add]
    have h18 : cos (A / 2 + B / 2) = cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2) := by
      rw [cos_add]
    rw [h17, h18]
    nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h3b, sq_pos_of_pos h4, sq_pos_of_pos h4b, Real.cos_sq_add_sin_sq (A / 2 + B / 2)]
  have h10 : cos (A / 2) * cos (B / 2) * cos (C / 2) ≠ 0 := by
    have ha : cos (A / 2) > 0 := h3
    have hb : cos (B / 2) > 0 := h3b
    have hc : cos (C / 2) > 0 := h3c
    have hpos : cos (A / 2) * cos (B / 2) * cos (C / 2) > 0 := by
      positivity
    positivity
  field_simp [h10] at h9 ⊢
  all_goals
    nlinarith