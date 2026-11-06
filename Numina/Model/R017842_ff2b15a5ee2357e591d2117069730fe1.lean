import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_315080 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (x^2 + 1) + sqrt ((4 - x)^2 + 4)) :
  IsLeast (range f) 5 := by

  constructor
  · -- Show 5 is in the range
    use 4 / 3
    rw [h₀]
    have h₁ : sqrt ((4 / 3 : ℝ) ^ 2 + 1) = (5 / 3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h₂ : sqrt ((4 - (4 / 3 : ℝ)) ^ 2 + 4) = (10 / 3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h₁, h₂]
    all_goals norm_num
  · -- Show there is no smaller value in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h₀] at hx
    have h1 : sqrt (x ^ 2 + 1) ≥ 0 := by positivity
    have h2 : sqrt ((4 - x) ^ 2 + 4) ≥ 0 := by positivity
    have h3 : sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4) ≥ 5 := by
      have h4 : (sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4)) ^ 2 ≥ 25 := by
        have h5 : (sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4)) ^ 2 =
          (sqrt (x ^ 2 + 1)) ^ 2 + (sqrt ((4 - x) ^ 2 + 4)) ^ 2 + 2 * (sqrt (x ^ 2 + 1) * sqrt ((4 - x) ^ 2 + 4)) := by ring
        rw [h5]
        have h6 : (sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 := by rw [Real.sq_sqrt]; nlinarith
        have h7 : (sqrt ((4 - x) ^ 2 + 4)) ^ 2 = (4 - x) ^ 2 + 4 := by rw [Real.sq_sqrt]; nlinarith
        rw [h6, h7]
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 1) - 5 / 3), sq_nonneg (sqrt ((4 - x) ^ 2 + 4) - 10 / 3), 
                  sq_nonneg (x - 4 / 3), 
                  mul_nonneg (Real.sqrt_nonneg (x^2 + 1)) (Real.sqrt_nonneg ((4 - x) ^ 2 + 4)), 
                  sq_nonneg (x - (4 - x) * (4 / 3)), 
                  mul_nonneg (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num)]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg ((4 - x) ^ 2 + 4)]
    linarith