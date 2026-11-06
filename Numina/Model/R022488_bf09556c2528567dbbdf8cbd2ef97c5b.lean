import Mathlib

theorem algebra_186287 (α : ℝ) (h : Real.cos (α - Real.pi / 2) = 0.2) (h1 : Real.pi / 2 < α ∧ α < Real.pi) :
    Real.tan (2 * α) = -4 * Real.sqrt 6 / 23 := by
  have h2 : Real.sin α = 0.2 := by
    have h' : Real.cos (α - Real.pi / 2) = Real.sin α := by
      rw [Real.cos_sub_pi_div_two]
    rw [h'] at h
    linarith
  have h3 : Real.pi / 2 < α := h1.1
  have h4 : α < Real.pi := h1.2
  have h5 : Real.cos α < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    all_goals linarith
  have h6 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
    have h' : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    nlinarith
  rw [h2] at h6
  have h8 : Real.cos α ^ 2 = (0.96 : ℝ) := by
    norm_num at h6 ⊢
    nlinarith
  have h10 : Real.cos α = -Real.sqrt (0.96 : ℝ) := by
    have h11 : Real.cos α ^ 2 = (0.96 : ℝ) := h8
    have h12 : Real.cos α < 0 := h5
    have h13 : Real.sqrt (0.96 : ℝ) ^ 2 = (0.96 : ℝ) := by 
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h14 : Real.sqrt (0.96 : ℝ) ≥ 0 := Real.sqrt_nonneg (0.96 : ℝ)
    nlinarith [Real.sqrt_nonneg (0.96 : ℝ), Real.sq_sqrt (show 0 ≤ (0.96 : ℝ) by norm_num)]
  have h10' : Real.sqrt (0.96 : ℝ) = (4 * Real.sqrt 6) / (10 : ℝ) := by
    have h2 : Real.sqrt (0.96 : ℝ) = Real.sqrt (96 / 100 : ℝ) := by norm_num
    rw [h2]
    have h7 : Real.sqrt ((96 / 100 : ℝ)) = Real.sqrt (96 : ℝ) / Real.sqrt (100 : ℝ) := by 
      field_simp [Real.sqrt_div]
      all_goals norm_num
    rw [h7]
    have h8 : Real.sqrt ((100 : ℝ)) = 10 := by
      rw [Real.sqrt_eq_cases]
      all_goals norm_num
    rw [h8]
    have h9 : Real.sqrt (96 : ℝ) = (4 : ℝ) * Real.sqrt 6 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (6 : ℝ))]
    rw [h9]
    all_goals ring_nf
  have h11 : Real.cos (2 * α) = 0.92 := by
    have hcos2 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    rw [hcos2, h8]
    all_goals norm_num
  have h12 : Real.sin (2 * α) = -0.16 * Real.sqrt 6 := by
    have hsin2 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by
      rw [Real.sin_two_mul]
    rw [hsin2, h2, h10, h10']
    all_goals 
      ring_nf 
      <;> norm_num
      <;> ring
      <;> norm_num
  have htan : Real.tan (2 * α) = Real.sin (2 * α) / Real.cos (2 * α) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan, h11, h12]
  have h13 : Real.sqrt 6 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> ring_nf