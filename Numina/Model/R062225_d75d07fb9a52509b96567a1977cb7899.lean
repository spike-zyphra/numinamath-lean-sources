import Mathlib

open Real Set
open scoped Real

theorem calculus_22786 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (hC1 : C = π / 2) (hA1 : sin A = 15 / 17) (hB1 : cos B = 15 / 17) :
  sin B = 8 / 17 := by
    rcases hA with ⟨ha1, ha2⟩
    rcases hB with ⟨hb1, hb2⟩
    rcases hC with ⟨hc1, hc2⟩
    have h1 : A + B = π / 2 := by 
      linarith [hABC, hC1]
    have h2 : sin B = cos A := by
      have hB_eq : B = π / 2 - A := by
        linarith [h1]
      rw [hB_eq]
      rw [sin_pi_div_two_sub]
    have h3 : cos A = (8 / 17 : ℝ) := by
      have hcosA : cos A ^ 2 + sin A ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq A
      rw [hA1] at hcosA
      have hcosA2 : cos A ^ 2 = (64 / 289 : ℝ) := by
        nlinarith
      have hcosA_pos : cos A > 0 := by
        have hA_lt_pi_div_two : A < π / 2 := by
          nlinarith [h1, hb1]
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [ha1, hA_lt_pi_div_two]
        · linarith [ha1, hA_lt_pi_div_two]
      nlinarith
    linarith [h2, h3]