import Mathlib

theorem algebra_2167 (f : ℝ → ℝ) (hf : f = fun x => 6 / x)
    (x₁ x₂ x₃ y₁ y₂ y₃ : ℝ)
    (hx₁ : f x₁ = y₁)
    (hx₂ : f x₂ = y₂)
    (hx₃ : f x₃ = y₃)
    (hx₁₂ : x₁ < x₂)
    (hx₂₀ : x₂ < 0)
    (hx₀₃ : 0 < x₃) :
    y₂ < y₁ ∧ y₁ < y₃ := by
  have h1 : y₁ = 6 / x₁ := by
    rw [hf] at hx₁
    linarith 
  have h2 : y₂ = 6 / x₂ := by 
    rw [hf] at hx₂
    linarith 
  have h3 : y₃ = 6 / x₃ := by 
    rw [hf] at hx₃
    linarith 
  have h4 : y₂ < y₁ := by
    rw [h2, h1]
    have h5 : x₁ < x₂ := by linarith 
    have h6 : x₂ < 0 := by linarith 
    have h7 : x₁ < 0 := by linarith 
    have h8 : x₁ ≠ 0 := by
      linarith 
    have h9 : x₂ ≠ 0 := by
      linarith 
    have h11 : 6 / x₂ < 6 / x₁ := by
      have h12 : (6 / x₂ : ℝ) - (6 / x₁ : ℝ) < 0 := by
        have h13 : (6 / x₂ : ℝ) - (6 / x₁ : ℝ) = (6 * (x₁ - x₂) ) / (x₁ * x₂) := by
          field_simp [(show x₁ ≠ 0 by assumption), (show x₂ ≠ 0 by assumption)]
          <;> ring
        rw [h13] 
        apply div_neg_of_neg_of_pos 
        · -- Show that 6 * (x₁ - x₂) < 0 
          nlinarith 
        · -- Show that x₁ * x₂ > 0 
          nlinarith [mul_pos_of_neg_of_neg (show (x₁ : ℝ) < 0 by linarith) (show (x₂ : ℝ) < 0 by linarith)]
      linarith 
    linarith 
  have h5 : y₁ < y₃ := by
    rw [h1, h3]
    have h6 : x₁ < 0 := by linarith 
    have h7 : x₃ > 0 := by linarith 
    have h8 : x₁ ≠ 0 := by
      linarith 
    have h9 : x₃ ≠ 0 := by
      linarith 
    have h11 : 6 / x₁ < 6 / x₃ := by
      have h12 : (6 / x₁ : ℝ) - (6 / x₃ : ℝ) < 0 := by
        have h13 : (6 / x₁ : ℝ) - (6 / x₃ : ℝ) = (6 * (x₃ - x₁) ) / (x₁ * x₃) := by
          field_simp [(show x₁ ≠ 0 by assumption), (show x₃ ≠ 0 by assumption)]
          <;> ring 
        rw [h13]
        apply div_neg_of_pos_of_neg 
        · -- Show that 6 * (x₃ - x₁) > 0 
          nlinarith 
        · -- Show that x₁ * x₃ < 0 
          nlinarith 
      linarith 
    linarith 
  constructor 
  · linarith [h4]
  · linarith [h5]