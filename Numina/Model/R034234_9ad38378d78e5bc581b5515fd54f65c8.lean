import Mathlib

open Real
open scoped Real

theorem calculus_15844 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π)
  (hA' : sin A = 3 / 5) (hB' : cos B = 5 / 13) :
  cos C = 16 / 65 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : cos A ^ 2 + sin A ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq A
  rw [hA'] at h1
  have h2 : cos A ^ 2 = 16 / 25 := by
    nlinarith
  have h3 : sin B ^ 2 + cos B ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq B
  rw [hB'] at h3
  have h4 : sin B ^ 2 = 144 / 169 := by
    nlinarith
  have h5 : 0 < sin B := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hB1, hB2]
    linarith [hB1, hB2]
  have h6 : sin B = 12 / 13 := by
    nlinarith
  have h7 : cos C = -cos (A + B) := by
    have h8 : C = π - (A + B) := by
      linarith [hABC]
    rw [h8]
    have h9 : cos (π - (A + B)) = -cos (A + B) := by
      rw [Real.cos_pi_sub]
    rw [h9]
  rw [h7]
  have hcos_add : cos (A + B) = cos A * cos B - sin A * sin B := by
    rw [Real.cos_add]
  rw [hcos_add, hA', hB', h6]
  have h9 : cos A ^ 2 = 16 / 25 := h2
  have h10 : cos A = 4 / 5 ∨ cos A = -4 / 5 := by
    have h11 : cos A ^ 2 - 16 / 25 = 0 := by linarith
    have h12 : (cos A - 4 / 5) * (cos A + 4 / 5) = 0 := by
      ring_nf at h11 ⊢
      linarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- cos A - 4/5 = 0, so cos A = 4/5
      left
      linarith
    · -- cos A + 4/5 = 0, so cos A = -4/5
      right
      linarith
  cases' h10 with hcosA1 hcosA2
  · rw [hcosA1]
    all_goals
      nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, 
                  Real.sin_pos_of_pos_of_lt_pi hA1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hB1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hC1 (by linarith)]
  · -- cos A = -4/5
    have h11 : cos A = -4 / 5 := hcosA2 
    have h8 : sin (A + B) < 0 := by
      have hsin_add : sin (A + B) = sin A * cos B + cos A * sin B := by
        rw [Real.sin_add]
      rw [hsin_add, hA', hB', h6, h11]
      norm_num
      all_goals nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, 
                  Real.sin_pos_of_pos_of_lt_pi hA1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hB1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hC1 (by linarith)]
    have h9 : 0 < A + B := by
      nlinarith [hA1, hB1, Real.pi_pos, Real.sin_pos_of_pos_of_lt_pi hA1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hB1 (by linarith)]
    have h10 : sin (A + B) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show angle A + B > 0
        exact_mod_cast h9
      · -- Show angle A + B < π
        nlinarith [hA2, hB2, Real.pi_pos, Real.sin_pos_of_pos_of_lt_pi hA1 (by linarith), 
                  Real.sin_pos_of_pos_of_lt_pi hB1 (by linarith)]
    linarith [h8, h10]
  -- Case cos A = 4/5 gives correct value
  all_goals
    linarith [hABC, hA1, hA2, hB1, hB2, hC1, hC2, h1, h2, h3, h4, h5, h6, h7, hcos_add, h9]