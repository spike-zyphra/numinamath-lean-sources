import Mathlib

theorem algebra_215940 (α β p : ℝ) (h₀ : Real.tan α + Real.tan β = -p) (h₁ : Real.tan α * Real.tan β = -Real.sqrt 3) (h₂ : α + β = Real.pi / 3) :
    p = -3 - Real.sqrt 3 := by

  have ha1 : Real.cos α ≠ 0 := by
    by_contra h
    have htanα : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [htanα] at h₁
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  
  have hb1 : Real.cos β ≠ 0 := by
    by_contra h
    have htanβ : Real.tan β = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h]
    rw [htanβ] at h₁
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
  
  have h3 : Real.tan (α + β) = Real.tan (Real.pi / 3) := by
    rw [h₂]

  have h4 : Real.tan (Real.pi / 3) = Real.sqrt 3 := Real.tan_pi_div_three

  have h5 : Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) := by
    rw [Real.tan_eq_sin_div_cos]
    have h6 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := Real.sin_add α β
    have h7 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := Real.cos_add α β
    rw [h6, h7]
    have h8 : Real.tan α = Real.sin α / Real.cos α := by rw [Real.tan_eq_sin_div_cos]
    have h9 : Real.tan β = Real.sin β / Real.cos β := by rw [Real.tan_eq_sin_div_cos]
    rw [h8, h9]
    field_simp [ha1, hb1]
    <;> ring

  have h10 : Real.tan (α + β) = Real.sqrt 3 := by
    rw [h3, h4]

  rw [h5] at h10 
  rw [show Real.tan α + Real.tan β = -p by linarith [h₀]] at h10
  rw [show 1 - Real.tan α * Real.tan β = 1 + Real.sqrt 3 by 
    nlinarith [h₁]
  ] at h10

  have h11 : Real.sqrt 3 * (1 + Real.sqrt 3) = -p := by
    field_simp [(show (1 + Real.sqrt 3) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    )] at h10 ⊢
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), h₁]

  have h12 : p = -3 - Real.sqrt 3 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), h₁]

  linarith