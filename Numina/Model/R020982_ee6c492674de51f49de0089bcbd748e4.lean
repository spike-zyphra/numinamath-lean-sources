import Mathlib

open Real Set
open scoped Real

theorem algebra_270881 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : sin α ^ 2 + sin β ^ 2 + sin γ ^ 2 = 1) :
    cos α * cos β * cos γ ≤ 2 * √6 / 9 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  rcases h₂ with ⟨h₂₁, h₂₂⟩
  have h₄ : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₀₁, h₀₂]
    linarith [h₀₁, h₀₂]
  have h₅ : cos β > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₁₁, h₁₂]
    linarith [h₁₁, h₁₂]
  have h₆ : cos γ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [h₂₁, h₂₂]
    linarith [h₂₁, h₂₂]
  have h10 : cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 = 2 := by
    have h11 : cos α ^ 2 + sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
    have h12 : cos β ^ 2 + sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    have h13 : cos γ ^ 2 + sin γ ^ 2 = 1 := Real.cos_sq_add_sin_sq γ
    nlinarith
  have h12 : cos α * cos β * cos γ ≤ 2 * Real.sqrt 6 / 9 := by
    have h13 : (cos α * cos β * cos γ) ^ 2 ≤ (8 / 27 : ℝ) := by
      nlinarith [sq_nonneg (cos α ^ 2 - cos β ^ 2), sq_nonneg (cos β ^ 2 - cos γ ^ 2), sq_nonneg (cos α ^ 2 - cos γ ^ 2),
                  sq_nonneg (cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 - 2), 
                  mul_pos h₄ h₅, mul_pos h₄ h₆, mul_pos h₅ h₆, 
                  mul_pos (show 0 < cos α ^ 2 by nlinarith) (show 0 < cos β ^ 2 by nlinarith), 
                  mul_pos (show 0 < cos β ^ 2 by nlinarith) (show 0 < cos γ ^ 2 by nlinarith), 
                  mul_pos (show 0 < cos α ^ 2 by nlinarith) (show 0 < cos γ ^ 2 by nlinarith)
                ]
    have h14 : (cos α * cos β * cos γ) ≤ Real.sqrt (8 / 27 : ℝ) := by
      have h15 : (Real.sqrt ( (cos α * cos β * cos γ) ^ 2 )) = cos α * cos β * cos γ := by
        rw [Real.sqrt_sq (show 0 ≤ cos α * cos β * cos γ by positivity)]
      have h16 : Real.sqrt ((cos α * cos β * cos γ) ^ 2) ≤ Real.sqrt (8 / 27 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      nlinarith
    have h15 : Real.sqrt (8 / 27 : ℝ) = 2 * Real.sqrt 6 / 9 := by
      have h17 : (8 / 27 : ℝ) = (2 * Real.sqrt 6 / 9) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by linarith)]
      have h18 : Real.sqrt (8 / 27 : ℝ) = (2 * Real.sqrt 6 / 9) := by
        rw [h17]
        field_simp
      linarith [h18]
    nlinarith [h14, h15]
  exact h12