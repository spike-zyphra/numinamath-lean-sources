import Mathlib

theorem algebra_189672 (A B C : Real) (hA : A ∈ Set.Ioo 0 (Real.pi / 2)) (hB : B ∈ Set.Ioo 0 (Real.pi / 2))
    (hC : C ∈ Set.Ioo 0 (Real.pi / 2)) (hABC : A + B + C = Real.pi) (h1 : Real.sin (A + B) = 3 / 5)
    (h2 : Real.sin (A - B) = 1 / 5) :
    Real.tan A = 2 * Real.tan B ∧ (A = 60 ∧ B = 30 ∧ C = 90 →
      (Real.sqrt ((Real.cos A) ^ 2 + (Real.sin A) ^ 2) * Real.sin B) / (Real.cos B) = 2 + Real.sqrt 6) := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h3 : Real.sin A * Real.cos B + Real.cos A * Real.sin B = 3 / 5 := by
    have h4 : Real.sin (A + B) = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
      rw [Real.sin_add]
    linarith [h1, h4]
  have h4 : Real.sin A * Real.cos B - Real.cos A * Real.sin B = 1 / 5 := by
    have h5 : Real.sin (A - B) = Real.sin A * Real.cos B - Real.cos A * Real.sin B := by
      rw [Real.sin_sub]
    linarith [h2, h5]
  have h5 : Real.sin A * Real.cos B = 2 / 5 := by
    linarith
  have h6 : Real.cos A * Real.sin B = 1 / 5 := by 
    linarith
  have htan : Real.tan A = 2 * Real.tan B := by
    have htanA : Real.tan A = Real.sin A / Real.cos A := by
      rw [Real.tan_eq_sin_div_cos]
    have htanB : Real.tan B = Real.sin B / Real.cos B := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htanA, htanB]
    have hc1 : Real.cos A ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [hA1, hA2, Real.pi_pos]
      linarith [hA1, hA2, Real.pi_pos]
    have hc2 : Real.cos B ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      linarith [hB1, hB2, Real.pi_pos]
      linarith [hB1, hB2, Real.pi_pos]
    have htan_eq : Real.sin A * Real.cos B = 2 * (Real.cos A * Real.sin B) := by
      linarith
    have hc1' : Real.cos A ≠ 0 := hc1
    have hc2' : Real.cos B ≠ 0 := hc2
    field_simp [hc1', hc2']
    linarith
  constructor
  · exact htan
  · intro h
    rcases h with ⟨hA_eq, hB_eq, hC_eq⟩
    have h_eq1 : Real.sqrt ((Real.cos A) ^ 2 + (Real.sin A) ^ 2) = 1 := by
      have h_eq2 : (Real.cos A) ^ 2 + (Real.sin A) ^ 2 = 1 := Real.cos_sq_add_sin_sq A
      rw [h_eq2]
      exact Real.sqrt_one
    have h_eq3 : Real.sqrt ((Real.cos A) ^ 2 + (Real.sin A) ^ 2) * Real.sin B = Real.sin B := by 
      rw [h_eq1]
      all_goals linarith
    rw [h_eq3]
    have hc2' : Real.cos B ≠ 0 := by
      have hcos1 : 0 < B := hB1
      have hcos2 : B < Real.pi / 2 := hB2
      have hcos3 : Real.cos B > 0 := by 
        apply Real.cos_pos_of_mem_Ioo
        constructor
        linarith [hcos1, hcos2, Real.pi_pos]
        linarith [hcos1, hcos2, Real.pi_pos]
      nlinarith
    field_simp [hc2']
    <;> nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, hABC, h1, h2, Real.sin_le_one A, Real.sin_le_one B, Real.sin_le_one C, Real.cos_pos_of_mem_Ioo (show A ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hA1, hA2, Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show B ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hB1, hB2, Real.pi_pos]), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : Real) ≤ 6 by norm_num)]