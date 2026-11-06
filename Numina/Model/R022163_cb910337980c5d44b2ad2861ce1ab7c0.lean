import Mathlib

theorem algebra_134769 (A B : Real) (hA : A ∈ Set.Ioo 0 (Real.pi / 2)) (hB : B ∈ Set.Ioo 0 (Real.pi / 2))
    (h : Real.tan (A + B) = 2 * Real.tan A) :
    Real.tan B ≤ Real.sqrt 2 / 4 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  have htanA : Real.tan A > 0 := by
    apply Real.tan_pos_of_pos_of_lt_pi_div_two
    all_goals
      try linarith [Real.pi_pos, hA1, hA2]
  have htanB : Real.tan B > 0 := by
    apply Real.tan_pos_of_pos_of_lt_pi_div_two
    all_goals
      try linarith [Real.pi_pos, hB1, hB2]
  have htanA_addB : 0 < A + B := by
    linarith
  have h2 : A + B < Real.pi := by
    linarith [Real.pi_pos, hA2, hB2]
  
  have h1 : Real.tan (A + B) = (Real.tan A + Real.tan B) / (1 - Real.tan A * Real.tan B) := by
    have h1a : Real.cos A > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [hA1, Real.pi_pos]
      · linarith [hA2, Real.pi_pos]
    
    have h1b : Real.cos B > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [hB1, Real.pi_pos]
      · linarith [hB2, Real.pi_pos]

    have htanA' : Real.tan A = Real.sin A / Real.cos A := by
      rw [Real.tan_eq_sin_div_cos]
    
    have htanB' : Real.tan B = Real.sin B / Real.cos B := by
      rw [Real.tan_eq_sin_div_cos]

    have htan_add : Real.tan (A + B) = Real.sin (A + B) / Real.cos (A + B) := by
      rw [Real.tan_eq_sin_div_cos]

    rw [htan_add]
    have htan_eq1 : Real.sin (A + B) = Real.sin A * Real.cos B + Real.cos A * Real.sin B := by
      rw [Real.sin_add]

    have htan_eq2 : Real.cos (A + B) = Real.cos A * Real.cos B - Real.sin A * Real.sin B := by
      rw [Real.cos_add]

    rw [htan_eq1, htan_eq2]

    have h3 : Real.cos A ≠ 0 := by
      nlinarith

    have h6 : Real.cos B ≠ 0 := by
      nlinarith
  
    rw [htanA', htanB']
  
    field_simp [h3, h6]
    <;> ring_nf <;> field_simp [h3, h6]
    <;> ring_nf
    <;> 
      try norm_num
    all_goals 
      try linarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B)] 
    <;> try norm_num
  
  rw [h1] at h
  have h2 : 1 - Real.tan A * Real.tan B ≠ 0 := by
    by_contra h3
    rw [h3] at h
    norm_num at h
    all_goals
      try linarith [htanA, htanB, sq_nonneg (Real.sin A), sq_nonneg (Real.sin B), sq_nonneg (Real.cos A), sq_nonneg (Real.cos B)]
  have h3 : Real.tan B = Real.tan A / (1 + 2 * Real.tan A ^ 2) := by
    field_simp at h ⊢
    <;> nlinarith
    <;> try norm_num
    <;> try linarith [sq_nonneg (Real.sin A * Real.sin B), sq_nonneg (Real.sin (A + B)), sq_nonneg (Real.sin A * Real.sin (A + B)), sq_nonneg (Real.tan A * Real.tan A), sq_nonneg (Real.tan (A + B)), sq_nonneg (Real.tan (B))]
  rw [h3]

  -- Now we need to find the maximum of tan B = tan A / (1 + 2*(tan A)^2) where tan A > 0
  have htanA_pos : Real.tan A > 0 := by
    linarith [htanA]
  
  have h5 : (0 : ℝ) < Real.sqrt 2 := by
    positivity
  have h7 : Real.sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  have h5 : Real.tan A / (1 + 2 * Real.tan A ^ 2) ≤ Real.sqrt 2 / 4 := by
    have htanA_pos : Real.tan A > 0 := by
      linarith [htanA]
    
    have h8 : 1 + 2 * Real.tan A ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos htanA_pos]

    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.tan A * Real.sqrt 2 - 1), sq_nonneg ((Real.tan A ^ 2 - 1 / 2)), sq_nonneg (Real.sqrt 2 ^ 2 - 2 * Real.tan A ^ 2), sq_nonneg (Real.tan A - Real.sqrt 2 / 2)] 
  linarith [sq_nonneg (Real.tan B - Real.sqrt 2 / 4), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
  all_goals
    try norm_num
    try linarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), sq_nonneg (4 * Real.tan B - Real.sqrt 2), sq_nonneg (Real.tan B * 2 * Real.sqrt 2 - 1)]
  all_goals try nlinarith
  <;> norm_num