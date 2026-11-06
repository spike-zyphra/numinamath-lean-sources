import Mathlib

open Real
open scoped Real

theorem inequalities_111852 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  6 ≤ 1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2) := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : sin (A / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h2 : sin (B / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h3 : sin (C / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h11 : sin (A / 2) + sin (B / 2) + sin (C / 2) ≤ 3 / 2 := by
    have h12 : A / 2 + B / 2 + C / 2 = π / 2 := by
      linarith
    have h21 : sin (A / 2) + sin (B / 2) + sin (C / 2) = sin (A / 2) + sin (B / 2) + cos (A / 2 + B / 2) := by
      have h13 : C / 2 = π / 2 - (A / 2 + B / 2) := by
        linarith
      have h14 : sin (C / 2) = cos (A / 2 + B / 2) := by
        rw [h13]
        have h15 : sin (π / 2 - (A / 2 + B / 2)) = cos (A / 2 + B / 2) := by
          rw [sin_pi_div_two_sub]
        linarith
      linarith
    rw [h21] at *
    have h100 : sin (A / 2) + sin (B / 2) + cos (A / 2 + B / 2) ≤ 3 / 2 := by
      have h13 : sin (A / 2) ≥ 0 := by positivity
      have h14 : sin (B / 2) ≥ 0 := by positivity
      have h18 : cos (A / 2 + B / 2) = cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2) := by
        rw [cos_add]
      rw [h18]
      have h21 : cos (A / 2) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos, hA1, hA2]
        · linarith [Real.pi_pos, hA1, hA2]
      have h21a : cos (B / 2) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos, hB1, hB2]
        · linarith [Real.pi_pos, hB1, hB2]
      nlinarith [sq_nonneg (sin (A / 2) - sin (B / 2)), sq_nonneg (sin (A / 2) - 1 / 2), sq_nonneg (sin (B / 2) - 1 / 2), sq_nonneg (cos (A / 2) - cos (B / 2)), sq_nonneg (cos (A / 2) - 1 / 2), sq_nonneg (cos (B / 2) - 1 / 2), Real.sin_sq_add_cos_sq (A / 2), Real.sin_sq_add_cos_sq (B / 2), sq_nonneg (sin (A / 2) + sin (B / 2) - 1 ), sq_nonneg (cos (A / 2) * cos (B / 2) - 1 / 4 )
          ]
    linarith
  have h14 : (1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2)) ≥ 9 / (sin (A / 2) + sin (B / 2) + sin (C / 2) ) := by
    have h14 : 0 < sin (A / 2) * sin (B / 2) * sin (C / 2) := by
      positivity
    have h15 : (1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2)) - 9 / (sin (A / 2) + sin (B / 2) + sin (C / 2) ) ≥ 0 := by
      have h15 : (1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2)) - 9 / (sin (A / 2) + sin (B / 2) + sin (C / 2) ) =
          ( (sin (A / 2) + sin (B / 2) + sin (C / 2) ) * (sin (A / 2) * sin (B / 2) + sin (A / 2) * sin (C / 2) + sin (B / 2) * sin (C / 2) ) - 9 * sin (A / 2) * sin (B / 2) * sin (C / 2) ) / ( (sin (A / 2) * sin (B / 2) * sin (C / 2) ) * (sin (A / 2) + sin (B / 2) + sin (C / 2) ) ) := by
        field_simp
        ring
      rw [h15]
      apply div_nonneg
      ·
        nlinarith [sq_nonneg (sin (A / 2) - sin (B / 2) ), sq_nonneg (sin (A / 2) - sin (C / 2) ), sq_nonneg (sin (B / 2) - sin (C / 2) ), mul_pos h1 (show 0 < sin (B / 2) by nlinarith), mul_pos h1 (show 0 < sin (C / 2) by nlinarith), mul_pos (show 0 < sin (B / 2) by nlinarith) (show 0 < sin (C / 2) by nlinarith) ]
      all_goals
        positivity
    linarith
  have h143 : (1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2) ) ≥ 6 := by
    have h27 : sin (A / 2) + sin (B / 2) + sin (C / 2) ≤ 3 / 2 := h11
    have h28 : sin (A / 2) + sin (B / 2) + sin (C / 2) > 0 := by positivity
    have h104 : (1 / sin (A / 2) + 1 / sin (B / 2) + 1 / sin (C / 2) ) ≥ 9 / (sin (A / 2) + sin (B / 2) + sin (C / 2) ) := h14
    have h102 : 9 / (sin (A / 2) + sin (B / 2) + sin (C / 2) ) ≥ 6 := by
      have h18 : sin (A / 2) + sin (B / 2) + sin (C / 2) > 0 := by positivity
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [h11]
    linarith
  linarith