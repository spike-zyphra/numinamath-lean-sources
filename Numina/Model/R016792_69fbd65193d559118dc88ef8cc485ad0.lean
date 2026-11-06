import Mathlib

open Real Set
open scoped Real

theorem algebra_11437 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π)
  (h : sin A + sqrt 3 * cos A = 2) :
  A = π / 6 := by
  rcases hA with ⟨hA1, hA2⟩
  have h1 : sin A + sqrt 3 * cos A = 2 * sin (A + Real.pi / 3) := by
    rw [Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring_nf
  rw [h1] at h
  have h2 : sin (A + Real.pi / 3) = 1 := by linarith
  have h3 : cos (A + Real.pi / 3) = 0 := by
    have h4 : cos (A + Real.pi / 3) ^ 2 + sin (A + Real.pi / 3) ^ 2 = 1 := Real.cos_sq_add_sin_sq (A + Real.pi / 3)
    rw [h2] at h4
    nlinarith
  have h4 : A + Real.pi / 3 = Real.pi / 2 := by
    have h5 : sin (A + Real.pi / 3) = 1 := h2
    have h6 : cos (A + Real.pi / 3) = 0 := h3
    have h7 : A + Real.pi / 3 = Real.pi / 2 := by
      have h8 : A + Real.pi / 3 ≥ Real.pi / 3 := by
        nlinarith [hA1, Real.pi_pos]
      have h9 : A + Real.pi / 3 ≤ Real.pi + Real.pi / 3 := by
        nlinarith [hA2, Real.pi_pos]
      by_cases h10 : A + Real.pi / 3 < Real.pi / 2
      · -- Assume A + π/3 < π/2
        have h11 : cos (A + Real.pi / 3) > 0 := by
          apply Real.cos_pos_of_mem_Ioo
          constructor
          · -- Show A + π/3 > -π/2
            nlinarith [hA1, Real.pi_pos]
          · -- Show A + π/3 < π/2
            linarith
        linarith [h6, h11]
      by_cases h12 : A + Real.pi / 3 > Real.pi / 2
      · -- Assume A + π/3 > π/2
        have h13 : cos (A + Real.pi / 3) < 0 := by
          apply Real.cos_neg_of_pi_div_two_lt_of_lt
          all_goals
          linarith [Real.pi_pos]
        linarith [h6, h13]
      · -- A + π/3 = π/2
        have h14 : A + Real.pi / 3 = Real.pi / 2 := by linarith
        exact h14
    linarith
  have h5 : A = Real.pi / 6 := by
    nlinarith [Real.pi_pos]
  exact h5