import Mathlib

theorem algebra_288960 {p q : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q)
    (x₁ x₂ : ℝ) (hx₁ : f x₁ = 0) (hx₂ : f x₂ = 0) (hne : x₁ ≠ 1 ∧ x₂ ≠ 1)
    (y₁ y₂ : ℝ) (hy₁ : y₁ = (x₁ + 1) / (x₁ - 1)) (hy₂ : y₂ = (x₂ + 1) / (x₂ - 1)) :
    (1 + p + q) * y₁^2 + 2 * (1 - q) * y₁ + 1 - p + q = 0 ∧
    (1 + p + q) * y₂^2 + 2 * (1 - q) * y₂ + 1 - p + q = 0 := by

  have h1 : x₁ ^ 2 + p * x₁ + q = 0 := by
    rw [hf] at hx₁
    simpa using hx₁

  have h2 : x₂ ^ 2 + p * x₂ + q = 0 := by 
    rw [hf] at hx₂
    simpa using hx₂
  
  have hx₁1_ne_1 : x₁ - 1 ≠ 0 := by
    intro h
    apply hne.1
    linarith

  have hx₂2_ne_1 : x₂ - 1 ≠ 0 := by
    intro h
    apply hne.2
    linarith
  
  constructor
  · -- Prove the first equation for y₁
    rw [hy₁]
    field_simp [(show x₁ - 1 ≠ 0 by assumption)]
    nlinarith [sq_pos_of_ne_zero (show x₁ - 1 ≠ 0 by assumption), sq_nonneg (x₁ + 1), sq_nonneg (x₁ - 1),
              h1, sq_nonneg (x₁ - 1)]
  
  · -- Prove the second equation for y₂
    rw [hy₂]
    field_simp [(show x₂ - 1 ≠ 0 by assumption)]
    nlinarith [sq_pos_of_ne_zero (show x₂ - 1 ≠ 0 by assumption), sq_nonneg (x₂ + 1), sq_nonneg (x₂ - 1),
              h2, sq_nonneg (x₂ - 1)]