import Mathlib

theorem algebra_282646 (A B C : ℝ) (hA : A ∈ Set.Ioo 0 (Real.pi)) (hB : B ∈ Set.Ioo 0 (Real.pi))
    (hC : C ∈ Set.Ioo 0 (Real.pi)) (hABC : A + B + C = Real.pi) :
    (Real.sin A + Real.sin B - Real.sin C) / (Real.sin A + Real.sin B + Real.sin C) =
    Real.tan (A / 2) * Real.tan (B / 2) := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have hC_eq : C = Real.pi - A - B := by
    linarith
  have h1 : Real.sin C = Real.sin (A + B) := by 
    rw [hC_eq]
    have h2 : Real.sin (Real.pi - A - B) = Real.sin (A + B) := by
      have h3 : Real.sin (Real.pi - A - B) = Real.sin (Real.pi - (A + B)) := by ring_nf
      rw [h3]
      rw [Real.sin_pi_sub]
      <;> ring_nf
    exact h2
  have h1' : Real.sin (A + B) = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by 
    rw [Real.sin_add]
  have htanA : Real.tan (A / 2) = Real.sin A / (1 + Real.cos A) := by 
    rw [Real.tan_eq_sin_div_cos]
    have hsinA : Real.sin A = 2 * Real.sin (A / 2) * Real.cos (A / 2) := by 
      rw [← Real.sin_two_mul (A / 2)]
      ring_nf
    have hcosA : Real.cos A = 2 * Real.cos (A / 2)^2 - 1 := by 
      have h : Real.cos A = Real.cos (2 * (A / 2)) := by ring_nf
      rw [h]
      rw [Real.cos_two_mul]
      <;> ring_nf
    rw [hsinA, hcosA]
    have hc : Real.cos (A / 2) ≠ 0 := by
      by_contra h0
      have h00 : Real.cos (A / 2) = 0 := by linarith
      have h11 : 0 < A / 2 := by linarith [hA1]
      have h22 : A / 2 < Real.pi / 2 := by linarith [hA2]
      have hcos_pos : Real.cos (A / 2) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith
        · linarith
      nlinarith
    have hne : 2 * Real.cos (A / 2) ^ 2 ≠ 0 := by
      intro h0
      have hc0 : Real.cos (A / 2) ^ 2 = 0 := by linarith
      have hc1 : Real.cos (A / 2) = 0 := by
        nlinarith
      contradiction
    field_simp [hc, hne]
    <;> ring_nf <;> field_simp [hc, hne]
    <;> ring_nf
    all_goals linarith
  have htanB : Real.tan (B / 2) = Real.sin B / (1 + Real.cos B) := by 
    rw [Real.tan_eq_sin_div_cos]
    have hsinB : Real.sin B = 2 * Real.sin (B / 2) * Real.cos (B / 2) := by 
      rw [← Real.sin_two_mul (B / 2)]
      ring_nf
    have hcosB : Real.cos B = 2 * Real.cos (B / 2)^2 - 1 := by 
      have h : Real.cos B = Real.cos (2 * (B / 2)) := by ring_nf
      rw [h]
      rw [Real.cos_two_mul]
      <;> ring_nf
    rw [hsinB, hcosB]
    have hc : Real.cos (B / 2) ≠ 0 := by
      by_contra h0
      have h00 : Real.cos (B / 2) = 0 := by linarith
      have h11 : 0 < B / 2 := by linarith [hB1]
      have h22 : B / 2 < Real.pi / 2 := by linarith [hB2]
      have hcos_pos : Real.cos (B / 2) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith
        · linarith
      nlinarith
    have hne : 2 * Real.cos (B / 2) ^ 2 ≠ 0 := by
      intro h0
      have hc0 : Real.cos (B / 2) ^ 2 = 0 := by linarith
      have hc1 : Real.cos (B / 2) = 0 := by
        nlinarith
      contradiction
    field_simp [hc, hne]
    <;> ring_nf <;> field_simp [hc, hne]
    <;> ring_nf
    all_goals linarith
  have h2 : Real.sin A > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hA1, hA2]
    linarith [hA1, hA2]
  have h3 : Real.sin B > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hB1, hB2]
    linarith [hB1, hB2]
  have h4 : Real.sin C > 0 := by
    have hC1' : 0 < C := by linarith [hC1, hC2]
    have hC2' : C < Real.pi := by linarith [hC1, hC2]
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hC1', hC2']
    linarith [hC1', hC2']
  have h3' : Real.sin A + Real.sin B + Real.sin C > 0 := by
    nlinarith
  rw [h1, h1']
  rw [htanA, htanB]
  <;> field_simp [show Real.sin A + Real.sin B + (Real.sin A * Real.cos B + Real.cos A * Real.sin B) ≠ 0 by nlinarith, show 1 + Real.cos A ≠ 0 by nlinarith [Real.sin_sq_add_cos_sq A, h2], show 1 + Real.cos B ≠ 0 by nlinarith [Real.sin_sq_add_cos_sq B, h3]]
  <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq, Real.sin_add, Real.cos_add]
  <;> nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), Real.sin_sq_add_cos_sq C, sq_nonneg (Real.sin (A / 2) - Real.sin (B / 2)), sq_nonneg (Real.cos (A / 2) - Real.cos (B / 2)), Real.sin_pos_of_pos_of_lt_pi (show 0 < A by linarith) (show A < Real.pi by linarith), Real.sin_pos_of_pos_of_lt_pi (show 0 < B by linarith) (show B < Real.pi by linarith), Real.sin_pos_of_pos_of_lt_pi (show 0 < C by linarith) (show C < Real.pi by linarith)]