import Mathlib

open Real Set
open scoped Real

theorem inequalities_219438 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  sin (A / 2) + sin (B / 2) + sin (C / 2) ≤
  1 + (1 / 2) * (cos ((A - B) / 4))^2 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have hC3 : C = π - (A + B) := by 
    linarith
  have hC4 : sin (C / 2) = cos ((A + B) / 2) := by 
    have h1 : C / 2 = Real.pi / 2 - (A + B) / 2 := by 
      rw [hC3]
      all_goals ring_nf
    rw [h1]
    have h2 : sin (Real.pi / 2 - (A + B) / 2) = cos ((A + B) / 2) := by
      rw [sin_pi_div_two_sub]
    exact h2
  rw [hC4]
  have eq1 : sin (A / 2) + sin (B / 2) = 2 * cos ((A - B) / 4) * sin ((A + B) / 4) := by 
    have h1 : sin (A / 2) + sin (B / 2) = 2 * sin ((A + B) / 4) * cos ((A - B) / 4) := by 
      have h2 : sin (A / 2) = sin (( (A + B) / 4 + (A - B) / 4 )) := by 
        ring_nf
      have h3 : sin (B / 2) = sin (( (A + B) / 4 - (A - B) / 4 )) := by 
        ring_nf
      rw [h2, h3]
      have h4 : sin (( (A + B) / 4 + (A - B) / 4 )) = sin (( (A + B) / 4 )) * cos (( (A - B) / 4 )) + cos (( (A + B) / 4 )) * sin (( (A - B) / 4 )) := by 
        rw [sin_add]
      have h5 : sin (( (A + B) / 4 - (A - B) / 4 )) = sin (( (A + B) / 4 )) * cos (( (A - B) / 4 )) - cos (( (A + B) / 4 )) * sin (( (A - B) / 4 )) := by 
        rw [sin_sub]
      rw [h4, h5]
      ring
    linarith
  rw [eq1]
  have h1 : cos ((A + B) / 2) = 1 - 2 * (sin ((A + B) / 4))^2 := by 
    have h4 : sin ((A + B) / 4) ^ 2 + cos ((A + B) / 4) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq ((A + B) / 4)
    have h5 : cos ((A + B) / 2) = 2 * (cos ((A + B) / 4))^2 - 1 := by 
      have h6 : cos ((A + B) / 2) = cos (2 * ((A + B) / 4)) := by ring_nf
      rw [h6]
      rw [cos_two_mul]
    nlinarith
  rw [h1]
  have h2 : sin ((A + B) / 4) ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi
    · -- Show 0 ≤ (A + B) / 4
      linarith [show A + B > 0 by linarith, show A + B < 2 * Real.pi by linarith [show A < Real.pi by linarith, show B < Real.pi by linarith]]
    · -- Show (A + B) / 4 ≤ Real.pi
      nlinarith [show A + B > 0 by linarith, show A + B < 2 * Real.pi by linarith [show A < Real.pi by linarith, show B < Real.pi by linarith]]
  have h3 : sin ((A + B) / 4) ≤ 1 := by 
    have h : sin ((A + B) / 4) ≤ 1 := by 
      linarith [sin_le_one ((A + B) / 4)]
    linarith
  have h41 : cos ((A - B) / 4) ≤ 1 := by 
    apply cos_le_one
  have h42 : -1 ≤ cos ((A - B) / 4) := by 
    apply neg_one_le_cos
  have h51 : cos ((A - B) / 4) ^ 2 ≥ 0 := by 
    positivity
  have h61 : sin ((A + B) / 4) ^ 2 ≥ 0 := by 
    positivity
  nlinarith [sq_nonneg (sin ((A + B) / 4) - cos ((A - B) / 4) / 2), sq_nonneg (cos ((A - B) / 4) ^ 2 - 2), sq_nonneg (cos ((A - B) / 4) - 1), sq_nonneg (sin ((A + B) / 4) - (1 / 2)), Real.sin_sq_add_cos_sq ((A - B) / 4), Real.sin_sq_add_cos_sq ((A + B) / 4)]