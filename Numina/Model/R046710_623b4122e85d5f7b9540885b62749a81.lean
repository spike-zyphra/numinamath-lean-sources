import Mathlib

open Real Set
open scoped Real

theorem algebra_293140 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (h : sin A * (cos (C / 2))^2 + sin C * (cos (A / 2))^2 = 3 / 2 * sin B) :
  cos ((A - C) / 2) - 2 * sin (B / 2) = 0 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : cos (C / 2) ^ 2 = (1 + cos C) / 2 := by
    have h1 : cos (C / 2) ^ 2 = (1 + cos C) / 2 := by
      have h3 : cos C = 2 * cos (C / 2) ^ 2 - 1 := by
        have h4 : cos (2 * (C / 2)) = 2 * cos (C / 2) ^ 2 - 1 := by
          rw [cos_two_mul]
        have h5 : 2 * (C / 2) = C := by ring
        rw [h5] at h4
        linarith
      linarith
    exact h1
  have h2 : cos (A / 2) ^ 2 = (1 + cos A) / 2 := by
    have h5 : cos (A / 2) ^ 2 = (1 + cos A) / 2 := by
      have h3 : cos A = 2 * cos (A / 2) ^ 2 - 1 := by
        have h4 : cos (2 * (A / 2)) = 2 * cos (A / 2) ^ 2 - 1 := by
          rw [cos_two_mul]
        have h5 : 2 * (A / 2) = A := by ring
        rw [h5] at h4
        linarith
      linarith
    exact h5
  rw [h1, h2] at h

  have h3 : sin A + sin C = 2 * sin B := by
    have eq1 : sin A * ((1 + cos C) / 2) + sin C * ((1 + cos A) / 2) = 3 / 2 * sin B := by
      linarith [h]
    have eq2 : sin A * ((1 + cos C) / 2) + sin C * ((1 + cos A) / 2) = (sin A + sin C + sin A * cos C + sin C * cos A) / 2 := by
      ring
    rw [eq2] at eq1
    have h4 : sin A * cos C + sin C * cos A = sin B := by
      have h5 : A + C = π - B := by linarith [hABC]
      have h6 : sin (A + C) = sin B := by
        rw [h5]
        have h7 : sin (π - B) = sin B := by
          rw [sin_pi_sub]
        linarith [h7]
      have h8 : sin (A + C) = sin A * cos C + cos A * sin C := by 
        rw [sin_add]
      linarith [h6, h8]
    linarith [eq1, h4]
  have hcos : cos (B / 2) ≠ 0 := by
    have hB1 : 0 < B := hB1
    have hB2 : B < π := hB2
    have h61 : 0 < B / 2 := by linarith
    have h62 : B / 2 < π / 2 := by 
      linarith
    have h60 : cos (B / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor 
      · linarith
      · linarith 
    nlinarith
  have h6 : cos ((A - C) / 2) = 2 * sin (B / 2) := by
    have eq43 : sin A + sin C = 2 * sin ((A + C) / 2) * cos ((A - C) / 2) := by
      have h10 : sin A + sin C = 2 * sin ((A + C) / 2) * cos ((A - C) / 2) := by
        rw [show A = (A + C) / 2 + (A - C) / 2 by ring]
        rw [show C = (A + C) / 2 - (A - C) / 2 by ring]
        rw [sin_add, sin_sub]
        ring
      linarith [h10]
    have eq44 : 2 * sin ((A + C) / 2) * cos ((A - C) / 2) = 2 * sin B := by
      linarith [h3, eq43]
    have eq45 : sin ((A + C) / 2) = cos (B / 2) := by 
      have h7 : A + C = π - B := by linarith [hABC]
      have h71 : (A + C) / 2 = (π - B) / 2 := by linarith [h7]
      rw [h71]
      have eqcos : sin ((π - B) / 2) = cos (B / 2) := by
        have h7 : (π - B) / 2 = π / 2 - B / 2 := by ring
        rw [h7]
        rw [sin_pi_div_two_sub]
      linarith [eqcos]
    rw [eq45] at eq44
    have eq46 : 2 * cos (B / 2) * cos ((A - C) / 2) = 2 * sin B := by
      nlinarith 
    have eqsin : sin B = 2 * sin (B / 2) * cos (B / 2) := by
      have h100 : sin B = 2 * sin (B / 2) * cos (B / 2) := by
        rw [show B = 2 * (B / 2) by ring]
        rw [sin_two_mul]
        <;> ring 
      linarith 
    rw [eqsin] at eq46
    have eq47 : cos ((A - C) / 2) = 2 * sin (B / 2) := by
      apply (mul_left_inj' hcos).mp
      linarith [eq46]
    linarith
  linarith [h6]