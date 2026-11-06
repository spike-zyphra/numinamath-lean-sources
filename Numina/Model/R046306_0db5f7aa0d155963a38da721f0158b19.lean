import Mathlib

open Real Set

theorem algebra_103852 (f : ℝ → ℝ) (hf : f = λ x => sqrt (x^2 + 2 * x + 10) + sqrt (x^2 - 2 * x + 10)) :
    IsLeast (range f) (2 * sqrt 10) := by
  have h1 : ∀ x, f x = sqrt (x^2 + 2 * x + 10) + sqrt (x^2 - 2 * x + 10) := by
    intro x
    rw [hf]

  have h2 : f 0 = 2 * sqrt 10 := by
    rw [h1]
    have h1' : sqrt (0^2 + 2 * 0 + 10) = sqrt 10 := by norm_num
    have h2' : sqrt (0^2 - 2 * 0 + 10) = sqrt 10 := by norm_num
    rw [h1', h2']
    all_goals ring

  constructor
  · -- Show 2 * sqrt 10 is indeed in the range
    use 0
    all_goals rw [h2]
  
  · -- Show 2 * sqrt 10 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h3 : sqrt (x^2 + 2 * x + 10) ≥ 0 := by positivity
    have h4 : sqrt (x^2 - 2 * x + 10) ≥ 0 := by positivity

    have h5 : sqrt (x^2 + 2 * x + 10) + sqrt (x^2 - 2 * x + 10) ≥ 2 * sqrt 10 := by
      have h7 : (sqrt (x^2 + 2 * x + 10) + sqrt (x^2 - 2 * x + 10)) ^2 ≥ (2 * sqrt 10) ^2 := by
        have h8 : (sqrt (x^2 + 2 * x + 10)) ^2 = x^2 + 2 * x + 10 := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x + 1)]
        have h9 : (sqrt (x^2 - 2 * x + 10)) ^2 = x^2 - 2 * x + 10 := by
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x - 1)]
        nlinarith [Real.sqrt_nonneg 10, 
          Real.sqrt_nonneg (x^2 + 2 * x + 10), 
          Real.sqrt_nonneg (x^2 - 2 * x + 10), 
          sq_nonneg (sqrt (x^2 + 2 * x + 10) - sqrt (x^2 - 2 * x + 10)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 + 2 * x + 10 : ℝ) by nlinarith [sq_nonneg (x + 1)]), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x^2 - 2 * x + 10 : ℝ) by nlinarith [sq_nonneg (x - 1)]), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + 2 * x + 10)) (Real.sqrt_nonneg (x^2 - 2 * x + 10)), 
          mul_nonneg (Real.sqrt_nonneg (10)) (Real.sqrt_nonneg (10)), 
          sq_nonneg (x * 0), 
          Real.sqrt_nonneg (10), 
          Real.sqrt_nonneg (10)]
      nlinarith [Real.sqrt_nonneg (x^2 + 2 * x + 10), 
        Real.sqrt_nonneg (x^2 - 2 * x + 10), 
        Real.sqrt_nonneg 10, 
        Real.sqrt_nonneg (10)]
    
    linarith [h5, hx]