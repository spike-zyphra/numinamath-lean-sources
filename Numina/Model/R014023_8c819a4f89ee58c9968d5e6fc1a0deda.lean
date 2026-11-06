import Mathlib

open Real
open scoped Real

theorem inequalities_170060 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  sin (A / 2) * sin (B / 2) * sin (C / 2) ≤ 1 / 8 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : A / 2 > 0 := by linarith
  have h2 : A / 2 < π / 2 := by
    linarith [hA2]
  have h3 : B / 2 > 0 := by linarith
  have h4 : B / 2 < π / 2 := by
    linarith [hB2]
  have h5 : C / 2 > 0 := by linarith
  have h6 : C / 2 < π / 2 := by
    linarith [hC2]
  have h7 : sin (A / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    . linarith
    . linarith [show A / 2 < π by linarith [hA2]]
  have h8 : sin (B / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    . linarith
    . linarith [show B / 2 < π by linarith [hB2]]
  have h9 : sin (C / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    . linarith
    . linarith [show C / 2 < π by linarith [hC2]]
  have h11 : sin (A / 2) * sin (B / 2) * sin (C / 2) ≤ 1 / 8 := by
    have h12 : C / 2 = π / 2 - (A / 2 + B / 2) := by
      linarith [hABC]
    have h13 : sin (C / 2) = cos (A / 2 + B / 2) := by
      rw [show C / 2 = π / 2 - (A / 2 + B / 2) by linarith [hABC]]
      rw [show sin (π / 2 - (A / 2 + B / 2)) = cos (A / 2 + B / 2) by
        rw [sin_pi_div_two_sub]
      ]
    rw [h13]
    have h14 : cos (A / 2 + B / 2) = cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2) := by
      rw [cos_add]
    rw [h14]
    have h15 : sin (A / 2) ^ 2 + cos (A / 2) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (A / 2)
    have h16 : sin (B / 2) ^ 2 + cos (B / 2) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (B / 2)
    have h17 : cos (A / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    have h18 : cos (B / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    nlinarith [sq_nonneg (sin (A / 2) - sin (B / 2)), sq_nonneg (sin (A / 2) - cos (A / 2)), sq_nonneg (sin (B / 2) - cos (B / 2)), sq_nonneg (cos (A / 2) - cos (B / 2)), sq_nonneg (sin (A / 2) * sin (B / 2) - 1 / 4), sq_nonneg (sin (A / 2) * cos (B / 2) - cos (A / 2) * sin (B / 2)), mul_pos h7 h8, mul_pos h7 h17, mul_pos h8 h18, mul_pos h17 h18]
  linarith