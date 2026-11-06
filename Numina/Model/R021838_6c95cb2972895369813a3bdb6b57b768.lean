import Mathlib

open Real Set
open scoped Real

theorem algebra_230222 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 = 1) :
    tan α * tan β * tan γ ≥ 2 * sqrt 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h4 : cos α > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h₀₁, h₀₂]
  have h5 : cos β > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h₁₁, h₁₂]
  have h6 : cos γ > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [h₂₁, h₂₂]
  have h7 : sin α > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₀₁, h₀₂]
    linarith [h₀₁, h₀₂]
  have h8 : sin β > 0 := by 
    apply sin_pos_of_pos_of_lt_pi 
    linarith [h₁₁, h₁₂]
    linarith [h₁₁, h₁₂]
  have h9 : sin γ > 0 := by 
    apply sin_pos_of_pos_of_lt_pi 
    linarith [h₂₁, h₂₂]
    linarith [h₂₁, h₂₂]
  have htanα : tan α = sin α / cos α := by 
    rw [tan_eq_sin_div_cos]
  have htanβ : tan β = sin β / cos β := by 
    rw [tan_eq_sin_div_cos]
  have htanγ : tan γ = sin γ / cos γ := by 
    rw [tan_eq_sin_div_cos]
  rw [htanα, htanβ, htanγ]
  have h13 : sin α * sin β * sin γ ≥ 2 * Real.sqrt 2 * (cos α * cos β * cos γ) := by 
    have h14 : sin α ^ 2 = 1 - cos α ^ 2 := by 
      have h15 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
      linarith 
    have h16 : sin β ^ 2 = 1 - cos β ^ 2 := by 
      have h17 : sin β ^ 2 + cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β 
      linarith 
    have h18 : sin γ ^ 2 = 1 - cos γ ^ 2 := by 
      have h19 : sin γ ^ 2 + cos γ ^ 2 = 1 := Real.sin_sq_add_cos_sq γ 
      linarith 
    have h22 : (sin α * sin β * sin γ) ^ 2 ≥ 8 * (cos α * cos β * cos γ) ^ 2 := by 
      rw [show (sin α * sin β * sin γ) ^ 2 = (sin α ^ 2) * (sin β ^ 2) * (sin γ ^ 2) by ring]
      rw [show (cos α * cos β * cos γ) ^ 2 = (cos α ^ 2) * (cos β ^ 2) * (cos γ ^ 2) by ring]
      rw [h14, h16, h18]
      have h29 : cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 = 1 := h₃
      have h23a : (cos α ^2 ) * (cos β ^2 ) * (cos γ ^2 ) > 0 := by positivity
      nlinarith [sq_nonneg (cos α ^2 - cos β ^2 ), sq_nonneg (cos α ^2 - cos γ ^2 ), 
          sq_nonneg (cos β ^2 - cos γ ^2 ), sq_nonneg (cos α ^2 * cos β ^2 - 1 / 9 ), 
          sq_nonneg (cos α ^2 * cos γ ^2 - 1 / 9 ), sq_nonneg (cos β ^2 * cos γ ^2 - 1 / 9 ), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_pos h4 h5, mul_pos h5 h6, mul_pos h4 h6, 
          sq_pos_of_pos h4, sq_pos_of_pos h5, sq_pos_of_pos h6, 
          h₃ 
          ]
    have h28a : sin α * sin β * sin γ ≥ 0 := by positivity 
    have h28b : cos α * cos β * cos γ ≥ 0 := by positivity 
    have h33a : (sin α * sin β * sin γ) ^ 2 ≥ (2 * Real.sqrt 2 * (cos α * cos β * cos γ) )^2 := by 
      nlinarith [h22, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
    have h34a : sin α * sin β * sin γ ≥ 2 * Real.sqrt 2 * (cos α * cos β * cos γ) := by 
      have h34a : (sin α * sin β * sin γ) ≥ 0 := h28a
      have h36a : 2 * Real.sqrt 2 * (cos α * cos β * cos γ) ≥ 0 := by positivity 
      nlinarith [h33a, mul_nonneg (show 0 ≤ (0 : ℝ) by norm_num) (show 0 ≤ (0 : ℝ) by norm_num) ]
    linarith
  have h14 : (sin α / cos α) * (sin β / cos β) * (sin γ / cos γ) = (sin α * sin β * sin γ) / (cos α * cos β * cos γ) := by
    field_simp [show cos α ≠ 0 by linarith, show cos β ≠ 0 by linarith, show cos γ ≠ 0 by linarith]
    <;> ring 
  rw [h14]
  have h15 : (sin α * sin β * sin γ) / (cos α * cos β * cos γ) ≥ 2 * Real.sqrt 2 := by 
    have hcos_pos : cos α * cos β * cos γ > 0 := by positivity 
    apply (le_div_iff₀ hcos_pos).mpr 
    linarith [h13]
  linarith [h15]