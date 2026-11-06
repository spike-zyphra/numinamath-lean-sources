import Mathlib

open Real Set
open scoped Real

theorem inequalities_309425 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    tan A * (cot B + cot C) + tan B * (cot C + cot A) + tan C * (cot A + cot B) ≥ 6 := by

  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩

  have htanA : 0 < tan A := by 
    have htanA_pos : 0 < tan A := by 
      rw [tan_eq_sin_div_cos]
      apply div_pos
      · -- Show 0 < sin A
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith 
      · -- Show 0 < cos A
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith
    linarith
  
  have htanB : 0 < tan B := by 
    have htanB_pos : 0 < tan B := by 
      rw [tan_eq_sin_div_cos]
      apply div_pos
      · -- Show 0 < sin B
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith 
      · -- Show 0 < cos B
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith 
    linarith
  
  have htanC : 0 < tan C := by 
    have htanC_pos : 0 < tan C := by 
      rw [tan_eq_sin_div_cos]
      apply div_pos
      · -- Show 0 < sin C
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith 
      · -- Show 0 < cos C
        apply cos_pos_of_mem_Ioo
        constructor <;> linarith 
    linarith
  
  have h1 : tan A * cot B + tan B * cot A ≥ 2 := by 
    have htanA : tan A = sin A / cos A := by rw [tan_eq_sin_div_cos]
    have htanB : tan B = sin B / cos B := by rw [tan_eq_sin_div_cos]
    have hcotB : cot B = cos B / sin B := by rw [cot_eq_cos_div_sin]
    have hcotA : cot A = cos A / sin A := by rw [cot_eq_cos_div_sin]
    rw [htanA, hcotB, htanB, hcotA]
    have hcosA_pos : 0 < cos A := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hcosB_pos : 0 < cos B := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hsinA_pos : 0 < sin A := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have hsinB_pos : 0 < sin B := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have h3 : (sin A / cos A) * (cos B / sin B) + (sin B / cos B) * (cos A / sin A) - 2 ≥ 0 := by
      have h4 : (sin A / cos A) * (cos B / sin B) + (sin B / cos B) * (cos A / sin A) - 2 =
          (sin A ^ 2 * cos B ^ 2 + sin B ^ 2 * cos A ^ 2 - 2 * (cos A * sin A * cos B * sin B)) / (cos A * sin A * cos B * sin B) := by 
        field_simp 
        <;> ring 
      rw [h4]
      apply div_nonneg
      · -- Prove that the numerator is non-negative 
        have h5 : sin A ^ 2 * cos B ^ 2 + sin B ^ 2 * cos A ^ 2 - 2 * (cos A * sin A * cos B * sin B) ≥ 0 := by 
          nlinarith [sq_nonneg (sin A * cos B - cos A * sin B), sq_nonneg (sin A - sin B), sq_nonneg (cos A - cos B), Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, mul_pos hsinA_pos hsinB_pos, mul_pos hcosA_pos hcosB_pos, mul_pos hsinA_pos hcosA_pos, mul_pos hsinB_pos hcosB_pos]
        linarith 
      · -- Prove that the denominator is non-negative 
        positivity 
    linarith

  have h2 : tan A * cot C + tan C * cot A ≥ 2 := by
    have htanA : tan A = sin A / cos A := by rw [tan_eq_sin_div_cos]
    have htanC : tan C = sin C / cos C := by rw [tan_eq_sin_div_cos]
    have hcotC : cot C = cos C / sin C := by rw [cot_eq_cos_div_sin]
    have hcotA : cot A = cos A / sin A := by rw [cot_eq_cos_div_sin]
    rw [htanA, hcotC, htanC, hcotA]
    have hcosA_pos : 0 < cos A := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hcosC_pos : 0 < cos C := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hsinA_pos : 0 < sin A := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have hsinC_pos : 0 < sin C := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have h4 : (sin A / cos A) * (cos C / sin C) + (sin C / cos C) * (cos A / sin A) - 2 ≥ 0 := by 
      have h5 : (sin A / cos A) * (cos C / sin C) + (sin C / cos C) * (cos A / sin A) - 2 = 
          (sin A ^ 2 * cos C ^ 2 + sin C ^ 2 * cos A ^ 2 - 2 * (cos A * sin A * cos C * sin C)) / (cos A * sin A * cos C * sin C) := by 
        field_simp 
        <;> ring 
      rw [h5] 
      apply div_nonneg 
      · -- Prove that the numerator is non-negative 
        have h6 : sin A ^ 2 * cos C ^ 2 + sin C ^ 2 * cos A ^ 2 - 2 * (cos A * sin A * cos C * sin C) ≥ 0 := by 
          nlinarith [sq_nonneg (sin A * cos C - cos A * sin C), sq_nonneg (sin A - sin C), sq_nonneg (cos A - cos C), Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq C, mul_pos hsinA_pos hsinC_pos, mul_pos hcosA_pos hcosC_pos, mul_pos hsinA_pos hcosA_pos, mul_pos hsinC_pos hcosC_pos]
        linarith 
      · -- Prove that the denominator is non-negative 
        positivity 
    linarith

  -- Similarly proving for the last pair.
  have h3 : tan B * cot C + tan C * cot B ≥ 2 := by
    have htanB : tan B = sin B / cos B := by rw [tan_eq_sin_div_cos]
    have htanC : tan C = sin C / cos C := by rw [tan_eq_sin_div_cos]
    have hcotC : cot C = cos C / sin C := by rw [cot_eq_cos_div_sin]
    have hcotB : cot B = cos B / sin B := by rw [cot_eq_cos_div_sin]
    rw [htanB, hcotC, htanC, hcotB]
    have hcosB_pos : 0 < cos B := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hcosC_pos : 0 < cos C := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos]
    have hsinB_pos : 0 < sin B := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have hsinC_pos : 0 < sin C := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos]
    have h4 : (sin B / cos B) * (cos C / sin C) + (sin C / cos C) * (cos B / sin B) - 2 ≥ 0 := by 
      have h5 : (sin B / cos B) * (cos C / sin C) + (sin C / cos C) * (cos B / sin B) - 2 = 
          (sin B ^ 2 * cos C ^ 2 + sin C ^ 2 * cos B ^ 2 - 2 * (cos B * sin B * cos C * sin C)) / (cos B * sin B * cos C * sin C) := by 
        field_simp 
        <;> ring 
      rw [h5] 
      apply div_nonneg 
      · -- Prove that the numerator is non-negative 
        have h6 : sin B ^ 2 * cos C ^ 2 + sin C ^ 2 * cos B ^ 2 - 2 * (cos B * sin B * cos C * sin C) ≥ 0 := by 
          nlinarith [sq_nonneg (sin B * cos C - cos B * sin C), sq_nonneg (sin B - sin C), sq_nonneg (cos B - cos C), Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, mul_pos hsinB_pos hsinC_pos, mul_pos hcosB_pos hcosC_pos, mul_pos hsinB_pos hcosB_pos, mul_pos hsinC_pos hcosC_pos]
        linarith 
      · -- Prove that the denominator is non-negative 
        positivity 
    linarith
  linarith [h1, h2, h3]