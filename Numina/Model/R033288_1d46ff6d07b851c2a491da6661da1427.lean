import Mathlib
open Real

theorem inequalities_5497 (α β γ : ℝ) (h₀ : α ∈ Set.Ioo 0 (π/2)) (h₁ : β ∈ Set.Ioo 0 (π/2)) (h₂ : γ ∈ Set.Ioo 0 (π/2)) :
    sin (α + β + γ) < sin α + sin β + sin γ := by
  rcases h₀ with ⟨h₁₀, h₂₀⟩
  rcases h₁ with ⟨h₃₀, h₄₀⟩
  rcases h₂ with ⟨h₅₀, h₆₀⟩

  have h₁₀₀ : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₁₀, h₂₀, Real.pi_pos]
    linarith [h₁₀, h₂₀, Real.pi_pos]

  have h₁₁₀ : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₁₀, h₂₀, Real.pi_pos]
    linarith [h₁₀, h₂₀, Real.pi_pos]

  have h₁₂₀ : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₃₀, h₄₀, Real.pi_pos]
    linarith [h₃₀, h₄₀, Real.pi_pos]

  have h₁₃₀ : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₃₀, h₄₀, Real.pi_pos]
    linarith [h₃₀, h₄₀, Real.pi_pos]

  have h₁₄₀ : sin γ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h₅₀, h₆₀, Real.pi_pos]
    linarith [h₅₀, h₆₀, Real.pi_pos]

  have h₁₅₀ : cos γ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₅₀, h₆₀, Real.pi_pos]
    linarith [h₅₀, h₆₀, Real.pi_pos]

  have h4 : sin (α + β + γ) = sin α * cos β * cos γ + cos α * sin β * cos γ + cos α * cos β * sin γ - sin α * sin β * sin γ := by
    rw [sin_add, sin_add]
    simp [sin_add, cos_add]
    <;> ring

  rw [h4]

  have h7 : sin α * cos β * cos γ < sin α := by
    have : cos β * cos γ < 1 := by
      have hcos1_lt1 : cos β < 1 := by
        have h2 : cos β < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₃₀, h₄₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos2_lt1 : cos γ < 1 := by
        have h2 : cos γ < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₅₀, h₆₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos1_pos : cos β > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₃₀, h₄₀, Real.pi_pos]
        linarith [h₃₀, h₄₀, Real.pi_pos]
      have hcos2_pos : cos γ > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₅₀, h₆₀, Real.pi_pos]
        linarith [h₅₀, h₆₀, Real.pi_pos]
      nlinarith
    nlinarith [h₁₀₀]

  have h8 : cos α * sin β * cos γ < sin β := by
    have : cos α * cos γ < 1 := by
      have hcos1_lt1 : cos α < 1 := by
        have h2 : cos α < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₁₀, h₂₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos2_lt1 : cos γ < 1 := by
        have h2 : cos γ < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₅₀, h₆₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos1_pos : cos α > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₁₀, h₂₀, Real.pi_pos]
        linarith [h₁₀, h₂₀, Real.pi_pos]
      have hcos2_pos : cos γ > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₅₀, h₆₀, Real.pi_pos]
        linarith [h₅₀, h₆₀, Real.pi_pos]
      nlinarith
    nlinarith [h₁₂₀]

  have h9 : cos α * cos β * sin γ < sin γ := by
    have : cos α * cos β < 1 := by
      have hcos1_lt1 : cos α < 1 := by
        have h2 : cos α < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₁₀, h₂₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos2_lt1 : cos β < 1 := by
        have h2 : cos β < cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [h₃₀, h₄₀, Real.pi_pos]
        rw [show cos (0 : ℝ) = 1 by exact cos_zero] at h2
        linarith
      have hcos1_pos : cos α > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₁₀, h₂₀, Real.pi_pos]
        linarith [h₁₀, h₂₀, Real.pi_pos]
      have hcos2_pos : cos β > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h₃₀, h₄₀, Real.pi_pos]
        linarith [h₃₀, h₄₀, Real.pi_pos]
      nlinarith
    nlinarith [h₁₄₀]

  have h10 : sin α * sin β * sin γ > 0 := by
    have h11 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h₁₀, h₂₀, Real.pi_pos]
      linarith [h₁₀, h₂₀, Real.pi_pos]
    have h22 : sin β > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h₃₀, h₄₀, Real.pi_pos]
      linarith [h₃₀, h₄₀, Real.pi_pos]
    have h33 : sin γ > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [h₅₀, h₆₀, Real.pi_pos]
      linarith [h₅₀, h₆₀, Real.pi_pos]
    positivity

  linarith [h7, h8, h9, h10]