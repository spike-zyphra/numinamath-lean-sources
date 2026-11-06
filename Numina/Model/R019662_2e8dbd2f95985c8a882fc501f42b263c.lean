import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_317084 :
  IsLeast {y | ∃ x : ℝ, y = 2 * x + sqrt (4 * x ^ 2 - 8 * x + 3)} 1 := by 
  constructor 
  · -- Show that 1 is in the image.
    use 1 / 2
    have h2 : sqrt (4 * (1 / 2 : ℝ) ^ 2 - 8 * (1 / 2 : ℝ) + 3) = 0 := by 
      rw [Real.sqrt_eq_zero'.mpr]
      norm_num 
      all_goals norm_num 
    rw [h2]
    all_goals norm_num 
  · -- Show that 1 is the least in the image.
    intro y hy 
    rcases hy with ⟨x, hx⟩
    by_cases h7 : x ≤ (1 / 2 : ℝ)
    · -- Case 1: x ≤ 1/2
      have h8 : 4 * x ^ 2 - 8 * x + 3 ≥ 0 := by 
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 3 / 2)]
      have h9 : sqrt (4 * x ^ 2 - 8 * x + 3) ≥ 0 := by positivity 
      have h5 : 2 * x + sqrt (4 * x ^ 2 - 8 * x + 3) ≥ 1 := by
        nlinarith [Real.sqrt_nonneg (4 * x ^ 2 - 8 * x + 3), 
          sq_nonneg (sqrt (4 * x ^ 2 - 8 * x + 3) - (1 - 2 * x)), 
          sq_nonneg (x - 1 / 2), 
          sq_nonneg (x - 3 / 2), 
          Real.sq_sqrt (show 0 ≤ (4 * x ^ 2 - 8 * x + 3 : ℝ) by nlinarith), 
          Real.sqrt_nonneg (4 * x ^ 2 - 8 * x + 3)
        ]
      linarith [hx, h5]
    · -- Case 2: x > 1/2 
      have h8 : x ≥ (1 / 2 : ℝ) := by linarith 
      by_cases h9 : x ≥ (3 / 2 : ℝ)
      · -- Case 2a: x ≥ 3/2 
        have h10 : 4 * x ^ 2 - 8 * x + 3 ≥ 0 := by 
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 3 / 2)]
        have h11 : sqrt (4 * x ^ 2 - 8 * x + 3) ≥ 0 := by positivity
        have h12 : 2 * x + sqrt (4 * x ^ 2 - 8 * x + 3) ≥ 1 := by
          nlinarith [Real.sqrt_nonneg (4 * x ^ 2 - 8 * x + 3), 
            sq_nonneg (sqrt (4 * x ^ 2 - 8 * x + 3) - (1 - 2 * x)), 
            sq_nonneg (x - 1 / 2), 
            sq_nonneg (x - 3 / 2), 
            Real.sq_sqrt (show 0 ≤ (4 * x ^ 2 - 8 * x + 3 : ℝ) by nlinarith), 
            Real.sqrt_nonneg (4 * x ^ 2 - 8 * x + 3)
          ]
        linarith [hx, h12]
      · -- Case 2b: 1/2 ≤ x < 3/2 
        have h10 : x < (3 / 2 : ℝ) := by linarith 
        have h11 : 4 * x ^ 2 - 8 * x + 3 < (0 : ℝ) := by 
          nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 3 / 2)]
        have h12 : sqrt (4 * x ^ 2 - 8 * x + 3) = 0 := by 
          rw [Real.sqrt_eq_zero'.mpr]
          linarith 
          all_goals linarith 
        have h13 : 2 * x + sqrt (4 * x ^ 2 - 8 * x + 3) ≥ 1 := by 
          rw [h12]
          nlinarith [sq_nonneg (x - 1 / 2)]
        linarith [hx, h13]