import Mathlib

open Real Set
open scoped Real

theorem inequalities_275292 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  sin (A / 2) * sin (B / 2) * sin (C / 2) < 1 / 4 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have hC_eq : C = π - A - B := by linarith
  have h1 : sin (C / 2) = cos ((A + B) / 2) := by
    rw [hC_eq]
    have : (π - A - B) / 2 = π / 2 - (A + B) / 2 := by
      linarith [pi_pos]
    rw [this]
    rw [sin_pi_div_two_sub]
  have h2 : sin (A / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [pi_pos]
  have h3 : sin (B / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [pi_pos]
  have h4 : cos ((A + B) / 2) > 0 := by 
    have h5 : 0 < (A + B) / 2 := by linarith
    have h6 : (A + B) / 2 < π / 2 := by
      have h7 : A + B < π := by
        nlinarith
      nlinarith [pi_pos]
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h5 : sin (A / 2) * sin (B / 2) * sin (C / 2) = sin (A / 2) * sin (B / 2) * cos ((A + B) / 2) := by 
    rw [h1]
  rw [h5]
  have h6 : sin (A / 2) * sin (B / 2) * cos ((A + B) / 2) < 1 / 4 := by
    have h7 : sin (A / 2) * sin (B / 2) > 0 := mul_pos h2 h3
    have h8 : cos ((A + B) / 2) > 0 := h4
    have h12 : cos ((A + B) / 2) = cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2) := by 
      have h13 : (A + B) / 2 = A / 2 + B / 2 := by ring
      rw [h13]
      rw [cos_add]
    rw [h12]
    have h10 : sin (A / 2) ^ 2 + cos (A / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (A / 2)
    have h11 : sin (B / 2) ^ 2 + cos (B / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (B / 2)
    nlinarith [sq_nonneg (sin (A / 2) - sin (B / 2)), sq_nonneg (sin (A / 2) ^ 2 - 1 / 4), sq_nonneg (sin (B / 2) ^ 2 - 1 / 4), 
      sq_nonneg (cos (A / 2) - cos (B / 2)), sq_nonneg (sin (A / 2) * sin (B / 2) - 1 / 4), 
      mul_pos h2 h3, 
      sq_nonneg (cos (A / 2) ^ 2 + cos (B / 2) ^ 2 - 1), 
      cos_sq_add_sin_sq (A / 2), 
      cos_sq_add_sin_sq (B / 2), 
      mul_pos h2 (show 0 < sin (B / 2) by linarith [h3]), 
      show 0 < sin (A / 2) * sin (B / 2) by positivity, 
      sq_nonneg (sin (A / 2) * sin (B / 2) * (cos (A / 2) * cos (B / 2) - sin (A / 2) * sin (B / 2)) - 1 / 4)
    ]
  linarith