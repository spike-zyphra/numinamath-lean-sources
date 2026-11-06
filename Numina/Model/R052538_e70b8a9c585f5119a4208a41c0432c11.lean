import Mathlib

open Real Set
open scoped Real

theorem algebra_278396 {α β : Real} (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : sin α ^ 2 + sin β ^ 2 = sin (α + β)) : α + β = π / 2 := by
  rcases h₀ with ⟨h₀₁, h₀₂⟩
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h3 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]
  rw [h3] at h₂
  by_cases h : α + β < π / 2
  · -- Assume α + β < π / 2, derive contradiction
    have h4 : β < π / 2 - α := by linarith
    have h5 : sin β < cos α := by
      have h6 : β < π / 2 - α := by linarith
      have h7 : sin β < sin (π / 2 - α) := by 
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h8 : sin (π / 2 - α) = cos α := by
        rw [sin_pi_div_two_sub]
      linarith
    have h9 : sin α < cos β := by
      have h10 : α < π / 2 - β := by linarith
      have h11 : sin α < sin (π / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h12 : sin (π / 2 - β) = cos β := by
        rw [sin_pi_div_two_sub]
      linarith
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith), Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith), h5, h9, Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(π / 2)) (π / 2) by constructor <;> nlinarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show β ∈ Ioo (-(π / 2)) (π / 2) by constructor <;> nlinarith [Real.pi_pos]), Real.sin_le_one α, Real.sin_le_one β, Real.sin_le_one (π / 2 - α), Real.sin_le_one (π / 2 - β)]
  by_cases h' : α + β > π / 2
  · -- Assume α + β > π / 2, derive contradiction
    have h5 : sin β > cos α := by
      have h6 : β > π / 2 - α := by linarith
      have h7 : sin β > sin (π / 2 - α) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h8 : sin (π / 2 - α) = cos α := by
        rw [sin_pi_div_two_sub]
      linarith
    have h9 : sin α > cos β := by
      have h10 : α > π / 2 - β := by linarith
      have h11 : sin α > sin (π / 2 - β) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos]
      have h12 : sin (π / 2 - β) = cos β := by
        rw [sin_pi_div_two_sub]
      linarith
    nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, Real.sin_pos_of_pos_of_lt_pi h₀₁ (show α < Real.pi by linarith), Real.sin_pos_of_pos_of_lt_pi h₁₁ (show β < Real.pi by linarith), h5, h9, Real.cos_pos_of_mem_Ioo (show α ∈ Ioo (-(π / 2)) (π / 2) by constructor <;> nlinarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show β ∈ Ioo (-(π / 2)) (π / 2) by constructor <;> nlinarith [Real.pi_pos]), Real.sin_le_one α, Real.sin_le_one β, Real.sin_le_one (π / 2 - α), Real.sin_le_one (π / 2 - β)]
  linarith [Real.pi_pos]