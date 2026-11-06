import Mathlib
open Real Set

theorem inequalities_1555 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π/2)) (h₁ : β ∈ Ioo 0 (π/2)) (h₂ : γ ∈ Ioo 0 (π/2)) (h₃ : tan α + tan β + tan γ = 3) :
    3 * √2 ≤ 1 / cos α + 1 / cos β + 1 / cos γ := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h₀₃ : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h₀₁, h₀₂, Real.pi_pos]
    · linarith [h₀₁, h₀₂, Real.pi_pos]
  have h₁₃ : 0 < cos β := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h₁₁, h₁₂, Real.pi_pos]
    · linarith [h₁₁, h₁₂, Real.pi_pos]
  have h₂₃ : 0 < cos γ := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h₂₁, h₂₂, Real.pi_pos]
    · linarith [h₂₁, h₂₂, Real.pi_pos]

  have htanα_pos : 0 < tan α := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith [h₀₁, Real.pi_pos]
    · linarith [h₀₂, Real.pi_pos]
  have htanβ_pos : 0 < tan β := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith [h₁₁, Real.pi_pos]
    · linarith [h₁₂, Real.pi_pos]
  have htanγ_pos : 0 < tan γ := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    · linarith [h₂₁, Real.pi_pos]
    · linarith [h₂₂, Real.pi_pos]

  have h₄ : 1 / cos α = Real.sqrt (1 + tan α ^ 2) := by
    have h5 : 1 + tan α ^ 2 = (1 / cos α) ^ 2 := by
      have htanα : tan α = sin α / cos α := by
        rw [tan_eq_sin_div_cos]
      rw [htanα]
      have h6 : cos α ≠ 0 := by
        nlinarith [h₀₃]
      field_simp [h6]
      <;> nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (sin α), sq_nonneg (cos α)]
    have h7 : (1 / cos α) ≥ 0 := by
      positivity
    have h8 : Real.sqrt (1 + tan α ^ 2) = (1 / cos α) := by
      rw [h5]
      rw [Real.sqrt_sq (show 0 ≤ (1 / cos α : ℝ) by linarith)]
    linarith [h8]

  have h₅ : 1 / cos β = Real.sqrt (1 + tan β ^ 2) := by
    have h6 : 1 + tan β ^ 2 = (1 / cos β) ^ 2 := by
      have htanβ : tan β = sin β / cos β := by
        rw [tan_eq_sin_div_cos]
      rw [htanβ]
      have h7 : cos β ≠ 0 := by
        nlinarith [h₁₃]
      field_simp [h7]
      <;> nlinarith [Real.sin_sq_add_cos_sq β, sq_nonneg (sin β), sq_nonneg (cos β)]
    have h8 : (1 / cos β) ≥ 0 := by
      positivity
    have h9 : Real.sqrt (1 + tan β ^ 2) = (1 / cos β) := by
      rw [h6]
      rw [Real.sqrt_sq (show 0 ≤ (1 / cos β : ℝ) by linarith)]
    linarith [h9]

  have h₆ : 1 / cos γ = Real.sqrt (1 + tan γ ^ 2) := by
    have h7 : 1 + tan γ ^ 2 = (1 / cos γ) ^ 2 := by
      have htanγ : tan γ = sin γ / cos γ := by
        rw [tan_eq_sin_div_cos]
      rw [htanγ]
      have h8 : cos γ ≠ 0 := by
        nlinarith [h₂₃]
      field_simp [h8]
      <;> nlinarith [Real.sin_sq_add_cos_sq γ, sq_nonneg (sin γ), sq_nonneg (cos γ)]
    have h9 : (1 / cos γ) ≥ 0 := by
      positivity
    have h10 : Real.sqrt (1 + tan γ ^ 2) = (1 / cos γ) := by
      rw [h7]
      rw [Real.sqrt_sq (show 0 ≤ (1 / cos γ : ℝ) by linarith)]
    linarith [h10]

  have h₇ : 1 / cos α + 1 / cos β + 1 / cos γ = Real.sqrt (1 + tan α ^ 2 ) + Real.sqrt (1 + tan β ^ 2 ) + Real.sqrt (1 + tan γ ^ 2 ) := by
    rw [h₄, h₅, h₆]

  have h₈ : Real.sqrt (1 + tan α ^ 2 ) + Real.sqrt (1 + tan β ^ 2 ) + Real.sqrt (1 + tan γ ^ 2 ) ≥ 3 * Real.sqrt 2 := by
    have h9 : ∀ t : ℝ, 0 ≤ t → Real.sqrt (1 + t^2) ≥ Real.sqrt 2 * (t + 1) / 2 := by
      intro t ht
      have h10 : Real.sqrt (1 + t^2) ≥ Real.sqrt 2 * (t + 1) / 2 := by
        have h11 : (Real.sqrt (1 + t^2) )^2 ≥ (Real.sqrt 2 * (t + 1) / 2) ^2 := by
          nlinarith [Real.sqrt_nonneg (1 + t ^ 2), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + t ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (t - 1), sq_nonneg (t * Real.sqrt 2 - Real.sqrt 2)]
        nlinarith [Real.sqrt_nonneg (1 + t^2), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + t ^ 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith
    have h10 : Real.sqrt (1 + tan α ^ 2 ) ≥ Real.sqrt 2 * (tan α + 1) / 2 := by
      apply h9
      nlinarith
    have h11 : Real.sqrt (1 + tan β ^ 2 ) ≥ Real.sqrt 2 * (tan β + 1) / 2 := by
      apply h9
      nlinarith
    have h12 : Real.sqrt (1 + tan γ ^ 2 ) ≥ Real.sqrt 2 * (tan γ + 1) / 2 := by
      apply h9
      nlinarith
    have h13 : Real.sqrt (1 + tan α ^ 2 ) + Real.sqrt (1 + tan β ^ 2 ) + Real.sqrt (1 + tan γ ^ 2 ) ≥ Real.sqrt 2 * ( (tan α + 1) + (tan β + 1) + (tan γ + 1) ) / 2 := by
      linarith
    have h14 : (tan α + 1) + (tan β + 1) + (tan γ + 1) = 6 := by
      nlinarith [h₃]
    nlinarith [Real.sqrt_nonneg 2, h14, sq_nonneg (Real.sqrt 2 * (tan α + 1) / 2), sq_nonneg (Real.sqrt 2 * (tan β + 1) / 2), sq_nonneg (Real.sqrt 2 * (tan γ + 1) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  
  linarith [h₇, h₈, Real.sqrt_nonneg 2]