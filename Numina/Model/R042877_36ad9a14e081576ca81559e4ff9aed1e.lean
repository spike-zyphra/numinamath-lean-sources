import Mathlib

open Real Set

theorem algebra_271612 :
    IsLeast {y | ∃ x : ℝ, y = sqrt (x^2 + 2 * x + 2) + sqrt (x^2 - 2 * x + 2)} (2 * sqrt 2) := by
  constructor
  · -- Show 2 * sqrt 2 is in the set
    use 0
    have h1 : sqrt (0 ^ 2 + 2 * (0 : ℝ) + 2) = sqrt 2 := by 
      norm_num
    have h2 : sqrt ((0 : ℝ) ^ 2 - 2 * (0 : ℝ) + 2) = sqrt 2 := by 
      norm_num
    rw [h1, h2]
    ring
  · -- Show 2 * sqrt 2 is minimal in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x ^ 2 + 2 * x + 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 2 * x + 2)
    have h2 : sqrt (x ^ 2 - 2 * x + 2) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 2 * x + 2)
    have h3 : x ^ 2 + 2 * x + 2 ≥ 0 := by 
      nlinarith [sq_nonneg (x + 1)]
    have h4 : x ^ 2 - 2 * x + 2 ≥ 0 := by 
      nlinarith [sq_nonneg (x - 1)]
    have h5 : sqrt (x^2 + 2 * x + 2) + sqrt (x^2 - 2 * x + 2) ≥ 2 * sqrt 2 := by 
      have h6 : (sqrt (x ^ 2 + 2 * x + 2) + sqrt (x ^ 2 - 2 * x + 2)) ^ 2 ≥ (2 * Real.sqrt 2) ^ 2 := by
        have h7 : (sqrt (x ^ 2 + 2 * x + 2) + sqrt (x ^ 2 - 2 * x + 2)) ^ 2 =
                  (sqrt (x ^ 2 + 2 * x + 2)) ^ 2 + (sqrt (x ^ 2 - 2 * x + 2)) ^ 2 + 2 * (sqrt (x^2 + 2 * x + 2) * sqrt (x^2 - 2 * x + 2)) := by 
                  ring
        have h8 : (2 * Real.sqrt 2) ^ 2 = 4 * (Real.sqrt 2) ^ 2 := by 
          ring
        rw [h7, h8]
        have h9 : (sqrt (x ^ 2 + 2 * x + 2)) ^ 2 = x ^ 2 + 2 * x + 2 := Real.sq_sqrt (by 
          nlinarith [sq_nonneg (x + 1)]
        )
        have h10 : (sqrt (x ^ 2 - 2 * x + 2)) ^ 2 = x ^ 2 - 2 * x + 2 := Real.sq_sqrt (by 
          nlinarith [sq_nonneg (x - 1)]
        )
        have h11 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        rw [h9, h10, h11]
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 2 * x + 2), Real.sqrt_nonneg (x ^ 2 - 2 * x + 2), 
          sq_nonneg (sqrt (x ^ 2 + 2 * x + 2) - sqrt (x^2 - 2 * x + 2)), 
          sq_nonneg (x ^ 2 + 2 * x + 2 - (x ^ 2 - 2 * x + 2)), 
          Real.sqrt_nonneg (2 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + 2 * x + 2)) (Real.sqrt_nonneg (x^2 - 2 * x + 2)), 
          sq_nonneg (x^2 - 2), 
          Real.sqrt_nonneg 2
        ]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 2 * x + 2), Real.sqrt_nonneg (x ^ 2 - 2 * x + 2), 
        Real.sqrt_nonneg (2 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      ]
    linarith [h5, hx]