import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_191110 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (1 + sin x) + sqrt (1 - sin x) +
    sqrt (2 + sin x) + sqrt (2 - sin x) + sqrt (3 + sin x) +
    sqrt (3 - sin x)) :
  IsGreatest (range f) (2 + 2 * sqrt 2 + 2 * sqrt 3) := by

  constructor
  · -- Show that the maximum value is in the range.
    use 0
    have h1 : sin (0 : ℝ) = 0 := by simp 
    rw [h₀ 0] 
    rw [h1]
    have h2 : sqrt (1 + (0 : ℝ)) = 1 := by
      rw [show (1 + (0 : ℝ)) = (1 : ℝ) by norm_num]
      exact sqrt_one 
    have h3 : sqrt (1 - (0 : ℝ)) = 1 := by
      rw [show (1 - (0 : ℝ)) = (1 : ℝ) by norm_num]
      exact sqrt_one 
    have h4 : sqrt (2 + (0 : ℝ)) = sqrt 2 := by
      norm_num
    have h5 : sqrt (2 - (0 : ℝ)) = sqrt 2 := by
      norm_num 
    have h6 : sqrt (3 + (0 : ℝ)) = sqrt 3 := by
      norm_num 
    have h7 : sqrt (3 - (0 : ℝ)) = sqrt 3 := by 
      norm_num 
    rw [h2, h3, h4, h5, h6, h7]
    all_goals ring 
  · -- Show that it's greatest.
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀ x] at hx 
    have h11 : sqrt (1 + sin x) + sqrt (1 - sin x) ≤ 2 := by 
      nlinarith [Real.sqrt_nonneg (1 + sin x), Real.sqrt_nonneg (1 - sin x),
          sq_nonneg (sqrt (1 + sin x) - sqrt (1 - sin x)), 
          Real.sq_sqrt (show 0 ≤ (1 + sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          Real.sq_sqrt (show 0 ≤ (1 - sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          sq_nonneg (sin x), 
          sin_le_one x, 
          neg_one_le_sin x 
        ]
    have h12 : sqrt (2 + sin x) + sqrt (2 - sin x) ≤ 2 * sqrt 2 := by 
      nlinarith [Real.sqrt_nonneg (2 + sin x), Real.sqrt_nonneg (2 - sin x), 
          sq_nonneg (sqrt (2 + sin x) - sqrt (2 - sin x)), 
          Real.sq_sqrt (show 0 ≤ (2 + sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          Real.sq_sqrt (show 0 ≤ (2 - sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          sq_nonneg (sin x), 
          Real.sqrt_nonneg (2 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          sin_le_one x, 
          neg_one_le_sin x 
        ]
    have h13 : sqrt (3 + sin x) + sqrt (3 - sin x) ≤ 2 * sqrt 3 := by 
      nlinarith [Real.sqrt_nonneg (3 + sin x), Real.sqrt_nonneg (3 - sin x), 
          sq_nonneg (sqrt (3 + sin x) - sqrt (3 - sin x)), 
          Real.sq_sqrt (show 0 ≤ (3 + sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          Real.sq_sqrt (show 0 ≤ (3 - sin x : ℝ) by linarith [neg_one_le_sin x, sin_le_one x]), 
          sq_nonneg (sin x), 
          Real.sqrt_nonneg (3 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sin_le_one x, 
          neg_one_le_sin x 
        ]
    have h14 : sqrt (1 + sin x) + sqrt (1 - sin x) + sqrt (2 + sin x) + sqrt (2 - sin x) + sqrt (3 + sin x) + sqrt (3 - sin x) ≤ 2 + 2 * sqrt 2 + 2 * sqrt 3 := by 
      linarith [h11, h12, h13]
    linarith [h14, hx]