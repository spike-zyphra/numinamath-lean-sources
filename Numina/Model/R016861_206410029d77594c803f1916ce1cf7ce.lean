import Mathlib

theorem algebra_311204 (α β : ℝ) (h₁ : Real.sin α = 5 / 7) (h₂ : Real.cos (α + β) = 11 / 14)
    (h₃ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₄ : β ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos β = (22 * Real.sqrt 6 + 25 * Real.sqrt 3) / 98 := by
  rcases h₃ with ⟨h₃₁, h₃₂⟩
  rcases h₄ with ⟨h₄₁, h₄₂⟩
  have h₅ : Real.cos α = 2 * Real.sqrt 6 / 7 := by
    have h₆ : Real.cos α > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, h₃₁, h₃₂]
      · linarith [Real.pi_pos, h₃₁, h₃₂]
    have h₇ : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    rw [h₁] at h₇
    have h₈ : Real.cos α ^ 2 = 24 / 49 := by nlinarith
    have h₉ : Real.cos α = Real.sqrt (24 / 49) := by
      have h₁₀ : Real.cos α ^ 2 = 24 / 49 := h₈
      have h₁₁ : Real.cos α ≥ 0 := by linarith [h₆]
      have h₁₂ : Real.cos α = Real.sqrt (Real.cos α ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ Real.cos α by linarith)]
      rw [h₁₂, h₁₀]
    have h₁₀ : Real.sqrt (24 / 49) = 2 * Real.sqrt 6 / 7 := by
      have h₁₁ : Real.sqrt (24 / 49) = Real.sqrt 24 / 7 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      have h₁₂ : Real.sqrt 24 = 2 * Real.sqrt 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h₁₁, h₁₂]
      <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h₉, h₁₀]
    all_goals linarith
  have h₁₂ : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    rw [Real.cos_add]
    all_goals linarith
  rw [h₁₂, h₁, h₅] at h₂
  have h₁₃ : Real.sin β > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos, h₄₁, h₄₂]
    · linarith [Real.pi_pos, h₄₁, h₄₂]
  have h₁₄ : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  have h₆ : Real.sin β = Real.sqrt (1 - Real.cos β ^ 2) := by
    have h₁₄' : Real.sin β ^ 2 = 1 - Real.cos β ^ 2 := by linarith
    have h₂₂ : Real.sin β ≥ 0 := by nlinarith
    have : Real.sin β = Real.sqrt (1 - Real.cos β ^ 2) := by
      rw [← h₁₄']
      field_simp [Real.sqrt_sq]
      all_goals linarith
    linarith
  rw [h₆] at h₂
  have h₇ : 0 < Real.sqrt 6 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  have h₈ : 0 < Real.sqrt 3 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  nlinarith [sq_nonneg (Real.sin β ^ 2 - 1 / 2), sq_nonneg (Real.cos β ^ 2 - ( (22 * Real.sqrt 6 + 25 * Real.sqrt 3) / 98) ^2), sq_nonneg (Real.cos β - (22 * Real.sqrt 6 + 25 * Real.sqrt 3) / 98), Real.sqrt_nonneg (1 - Real.cos β ^ 2), 
            Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, Real.sqrt_nonneg 18, Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 2, 
            Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (18 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (24 / 49 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]