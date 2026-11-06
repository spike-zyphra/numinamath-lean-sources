import Mathlib

open Real

theorem inequalities_144601 (f : ℝ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : p + q = 1) (x₁ x₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    p * sqrt x₁ + q * sqrt x₂ ≤ sqrt (p * x₁ + q * x₂) := by
  have h1 : q = 1 - p := by linarith
  rw [h1]
  have h2 : 0 ≤ p * x₁ + (1 - p) * x₂ := by
    nlinarith [hx₁, hx₂, hp, show 0 ≤ 1 - p by nlinarith]

  have h3 : p * sqrt x₁ + (1 - p) * sqrt x₂ ≤ sqrt (p * x₁ + (1 - p) * x₂) := by
    have h4 : (p * sqrt x₁ + (1 - p) * sqrt x₂) ^ 2 ≤ (sqrt (p * x₁ + (1 - p) * x₂)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (p * x₁ + (1 - p) * x₂), Real.sqrt_nonneg x₁, Real.sqrt_nonneg x₂, 
        Real.sq_sqrt (show 0 ≤ p * x₁ + (1 - p) * x₂ by nlinarith), 
        Real.sq_sqrt (show 0 ≤ x₁ by linarith), 
        Real.sq_sqrt (show 0 ≤ x₂ by linarith), 
        sq_nonneg (sqrt (p * x₁ + (1 - p) * x₂) - p * sqrt x₁ - (1 - p) * sqrt x₂), 
        sq_nonneg (sqrt x₁ - sqrt x₂), 
        hp, show 0 < (1 - p) by nlinarith, 
        mul_nonneg (Real.sqrt_nonneg x₁) (Real.sqrt_nonneg x₂), 
        Real.sqrt_le_sqrt (show 0 ≤ x₁ by linarith), 
        Real.sqrt_le_sqrt (show 0 ≤ x₂ by linarith), 
        mul_nonneg (show 0 ≤ p by linarith) (show 0 ≤ (1 - p) by nlinarith)]
    have h5 : p * sqrt x₁ + (1 - p) * sqrt x₂ ≤ sqrt (p * x₁ + (1 - p) * x₂) := by
      nlinarith [Real.sqrt_nonneg (p * x₁ + (1 - p) * x₂), Real.sqrt_nonneg x₁, Real.sqrt_nonneg x₂, h4, mul_nonneg (show (0 : ℝ) ≤ p by linarith) (show (0 : ℝ) ≤ (1 - p) by nlinarith)]
    exact h5
  exact h3