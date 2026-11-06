import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316336 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (x^2 + 2 * x + 2) + sqrt (x^2 - 2 * x + 2)) :
  IsLeast {y | ∃ x, y = f x} (2 * sqrt 2) := by

  constructor
  · -- Prove 2 * sqrt(2) is in the set {y | ∃ x, y = f x}
    use 0
    rw [h₀]
    have h1 : sqrt (0 ^ 2 + 2 * (0 : ℝ) + 2) = Real.sqrt 2 := by
      norm_num
    have h2 : sqrt (0 ^ 2 - 2 * (0 : ℝ) + 2) = Real.sqrt 2 := by
      norm_num
    rw [h1, h2]
    have h3 : Real.sqrt 2 + Real.sqrt 2 = 2 * Real.sqrt 2 := by
      ring
    linarith [h3]
  · -- Prove 2 * sqrt(2) is the least such value
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    have h1 : sqrt (x ^ 2 + 2 * x + 2) ≥ 0 := by positivity
    have h2 : sqrt (x ^ 2 - 2 * x + 2) ≥ 0 := by positivity
    have h3 : (sqrt (x^2 + 2 * x + 2) + sqrt (x^2 - 2 * x + 2)) ^ 2 ≥ (2 * Real.sqrt 2) ^ 2 := by
      have h4 : sqrt (x ^ 2 + 2 * x + 2) ^ 2 = x^2 + 2 * x + 2 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (x + 1)]
      have h5 : sqrt (x ^ 2 - 2 * x + 2) ^ 2 = x^2 - 2 * x + 2 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (x - 1)]
      nlinarith [sq_nonneg (sqrt (x^2 + 2 * x + 2) - sqrt (x^2 - 2 * x + 2)), sq_nonneg (x), 
                sq_nonneg (x + 1), sq_nonneg (x - 1), 
                Real.sqrt_nonneg 2, 
                Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                Real.sqrt_nonneg (x^2 + 2 * x + 2), 
                Real.sqrt_nonneg (x^2 - 2 * x + 2), 
                mul_nonneg (Real.sqrt_nonneg (x^2 + 2 * x + 2)) (Real.sqrt_nonneg (x^2 - 2 * x + 2)), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + 2 * x + 2 : ℝ) by nlinarith [sq_nonneg (x + 1)]), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 - 2 * x + 2 : ℝ) by nlinarith [sq_nonneg (x - 1)])
              ]
    have h4 : sqrt (x ^ 2 + 2 * x + 2) + sqrt (x ^ 2 - 2 * x + 2) ≥ 2 * Real.sqrt 2 := by
      nlinarith [show 0 ≤ (sqrt (x ^ 2 + 2 * x + 2) - sqrt (x ^ 2 - 2 * x + 2)) ^ 2 by positivity, 
        Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        h3, 
        sq_nonneg (sqrt (x^2 + 2 * x + 2) - sqrt (x^2 - 2 * x + 2)), sq_nonneg (2 * Real.sqrt 2)
      ]
    linarith [h4, hx]