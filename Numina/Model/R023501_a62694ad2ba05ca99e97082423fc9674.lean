import Mathlib

theorem algebra_311338 (A B : ℝ) (hA : A ∈ Set.Ioo 0 (Real.pi / 2)) (hB : B ∈ Set.Ioo 0 (Real.pi / 2))
    (h : Real.sin A / Real.sin B = Real.cos (A + B)) :
    Real.tan A ≤ Real.sqrt 2 / 4 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  have h1 : Real.sin B > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos, hB1, hB2]
    linarith [Real.pi_pos, hB1, hB2]
  have h2 : Real.cos B > 0 := by 
    apply Real.cos_pos_of_mem_Ioo 
    constructor <;> linarith [Real.pi_pos, hB1, hB2]
  have h3 : Real.sin A > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi 
    linarith [Real.pi_pos, hA1, hA2]
    linarith [Real.pi_pos, hA1, hA2]
  have h4 : Real.cos A > 0 := by 
    apply Real.cos_pos_of_mem_Ioo 
    constructor <;> linarith [Real.pi_pos, hA1, hA2]
  have h5 : Real.cos (A + B) = Real.cos A * Real.cos B - Real.sin A * Real.sin B := by
    exact Real.cos_add A B
  have h6 : Real.sin A / Real.sin B = Real.cos (A + B) := by
    linarith [h]
  rw [h5] at h6
  have h7 : Real.sin A = Real.sin B * (Real.cos A * Real.cos B - Real.sin A * Real.sin B) := by 
    have h7 : Real.sin B > 0 := h1
    have eq1 : Real.sin A / Real.sin B = Real.cos A * Real.cos B - Real.sin A * Real.sin B := by 
      linarith [h6]
    have eq2 : Real.sin A = Real.sin B * (Real.cos A * Real.cos B - Real.sin A * Real.sin B) := by 
      field_simp [h7] at eq1 ⊢ 
      linarith [eq1]
    linarith [eq2]
  have h8 : Real.sin A * (1 + Real.sin B ^ 2) = Real.sin B * (Real.cos A * Real.cos B) := by 
    nlinarith [h7]
  have h9 : Real.sin A / Real.cos A = Real.sin B * Real.cos B / (1 + Real.sin B ^ 2) := by 
    have eq1 : Real.sin A / Real.cos A = Real.sin B * (Real.cos A * Real.cos B) / (Real.cos A * (1 + Real.sin B ^ 2)) := by 
      have h4' : Real.cos A ≠ 0 := by nlinarith [h4]
      have h10 : Real.sin A * (1 + Real.sin B ^ 2) = Real.sin B * (Real.cos A * Real.cos B) := by linarith [h8]
      have h11 : Real.cos A * (1 + Real.sin B ^ 2) ≠ 0 := by
        apply mul_ne_zero
        linarith [h4]
        nlinarith [h1, Real.sin_sq_add_cos_sq B]
      field_simp [h11]
      <;> nlinarith [h10]
    have eq2 : Real.sin B * (Real.cos A * Real.cos B) / (Real.cos A * (1 + Real.sin B ^ 2)) = Real.sin B * Real.cos B / (1 + Real.sin B ^ 2) := by 
      have h4' : Real.cos A ≠ 0 := by nlinarith [h4]
      field_simp [h4']
      <;> ring_nf <;> field_simp
    rw [eq1, eq2]
  have htan : Real.tan A = Real.sin B * Real.cos B / (1 + Real.sin B ^ 2) := by 
    rw [Real.tan_eq_sin_div_cos]
    linarith [h9]
  rw [htan]
  have h10 : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
  have h11 : Real.sin B * Real.cos B ≤ Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2) := by 
    have h12 : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
    have h13 : 0 < Real.sin B := h1
    have h14 : 0 < Real.cos B := h2
    have h15 : Real.sin B * Real.cos B ≤ Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2) := by 
      have h16 : (Real.sin B * Real.cos B) ^ 2 ≤ (1 / 8) * (1 + Real.sin B ^ 2) ^ 2 := by 
        nlinarith [sq_nonneg (Real.sin B ^ 2 - 1 / 3), sq_nonneg (Real.cos B ^ 2 - 2 / 3), sq_nonneg (Real.sin B ^ 2 - Real.cos B ^ 2), Real.sin_sq_add_cos_sq B, sq_nonneg (Real.sin B - Real.cos B), sq_nonneg (Real.sin B * Real.cos B * 4), sq_nonneg (Real.sin B ^ 2 - 1 / 3), sq_nonneg ((1 + Real.sin B ^ 2) ^ 2 - 4 * (Real.sin B * Real.cos B) ^ 2 * 8), mul_pos h1 h2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h17 : Real.sin B * Real.cos B ≥ 0 := by 
        nlinarith [h1, h2]
      have h18 : Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2) ≥ 0 := by 
        positivity
      have h19 : (Real.sin B * Real.cos B) ^ 2 ≤ (Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2)) ^ 2 := by
        nlinarith [h16, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (1 + Real.sin B ^ 2 - Real.sqrt 2 * (Real.sin B * Real.cos B) / 2), sq_nonneg ((Real.sin B * Real.cos B) - Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2))]
      have h20 : Real.sin B * Real.cos B ≤ Real.sqrt 2 / 4 * (1 + Real.sin B ^ 2) := by 
        nlinarith [h19, h17, h18, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith
    linarith
  have h12 : 0 < (1 + Real.sin B ^ 2) := by 
    nlinarith [Real.sin_le_one B, h1, h2, Real.sin_sq_add_cos_sq B]
  have h14 : Real.sin B * Real.cos B / (1 + Real.sin B ^ 2) ≤ Real.sqrt 2 / 4 := by 
    apply (div_le_iff₀ (by linarith)).mpr 
    nlinarith [h11, sq_nonneg (1 + Real.sin B ^ 2), h1, h2, sq_nonneg (Real.sin B * Real.cos B), sq_nonneg (Real.cos B), sq_nonneg (Real.sin B ^ 2 - 1 / 3), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  linarith [h14]